-- | Entry point for Hydra type inference, which is a variation on on Hindley-Milner

module Hydra.Inference (
  annotateTermWithTypes,
  inferGraphTypes,
  inferType,
  inferTypeAndConstraints,
  Constraint,
) where

import Hydra.Basics
import Hydra.Compute
import Hydra.Core
import Hydra.CoreDecoding
import Hydra.CoreEncoding
import Hydra.Graph
import Hydra.Kv
import Hydra.Lexical
import Hydra.Mantle
import Hydra.Reduction
import Hydra.Rewriting
import Hydra.Strip
import Hydra.Substitution
import Hydra.Tier1
import Hydra.Tier2
import Hydra.Tools.Debug
import Hydra.Tools.Sorting
import Hydra.Unification

import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


data Inferred a = Inferred {
  -- The original term, possibly annotated with the inferred type
  inferredTerm :: Term,
  -- The inferred type
  inferredType :: Type Kv,
  -- Any constraints introduced by the inference process
  inferredConstraints :: [Constraint Kv]
}

annotateElements :: Graph Kv -> [Element Kv] -> Flow (Graph Kv) [Element Kv]
annotateElements g sortedEls = initializeGraph $ do
    rels <- annotate sortedEls []

    -- Note: inference occurs over the entire graph at once,
    --       but unification and substitution occur within elements in isolation
    let constraints = inferredConstraints . snd <$> rels
    subst <- withSchemaContext $ CM.mapM solveConstraints constraints
    CM.zipWithM rewriteElement subst rels
  where
    rewriteElement subst (name, rel) = do
        anns <- graphAnnotations <$> getState
        term <- substituteAndNormalizeAnnotations anns subst $ inferredTerm rel
        return $ Element name term

    annotate original annotated = case original of
      [] -> pure $ L.reverse annotated
      (el:rest) -> do
        rel <- inferElementType el
        withBinding (fst rel) (inferredType $ snd rel) $ annotate rest (rel:annotated)

annotateTermWithTypes :: Term -> Flow (Graph Kv) (Term)
annotateTermWithTypes = inferTypeAndConstraints

-- Decode a type, eliminating nominal types for the sake of unification
decodeStructuralType :: Term -> Flow (Graph Kv) (Type Kv)
decodeStructuralType term = do
  typ <- coreDecodeType term
  let typ' = stripType typ
  case typ' of
    TypeVariable name -> withSchemaContext $ withTrace "decode structural type" $ do
      el <- requireElement name
      decodeStructuralType $ elementData el
    _ -> pure typ

findMatchingField :: FieldName -> [FieldType Kv] -> Flow (Graph Kv) (FieldType Kv)
findMatchingField fname sfields = case L.filter (\f -> fieldTypeName f == fname) sfields of
  []    -> fail $ "no such field: " ++ unFieldName fname
  (h:_) -> return h

freshName :: Flow (Graph Kv) Name
freshName = normalVariable <$> nextCount "hyInf"

freshTypeVariable :: Flow (Graph Kv) (Type Kv)
freshTypeVariable = TypeVariable <$> freshName

infer :: Term -> Flow (Graph Kv) (Inferred Kv)
infer term = case term of
    TermAnnotated (Annotated subj ann) -> do
      rsubj <- infer subj

      anns <- graphAnnotations <$> getState
      otyp <- annotationClassTermType anns term
      let constraints = (inferredConstraints rsubj) ++ case otyp of
            Nothing -> []
            Just t -> [(inferredType rsubj, t)]

      yieldTerm (TermAnnotated $ Annotated (inferredTerm rsubj) ann) (inferredType rsubj) constraints

    TermApplication (Application fun arg) -> do
      rfun <- infer fun
      rarg <- infer arg
      cod <- freshTypeVariable
      let constraints = (inferredConstraints rfun) ++ (inferredConstraints rarg)
            ++ [(inferredType rfun, Types.function (inferredType rarg) cod)]
      yieldTerm (TermApplication $ Application (inferredTerm rfun) (inferredTerm rarg)) cod constraints

    TermFunction f -> case f of

      FunctionElimination e -> case e of

        EliminationList fun -> do
          a <- freshTypeVariable
          b <- freshTypeVariable
          let expected = Types.function b (Types.function a b)
          rfun <- infer fun
          let elim = Types.function b (Types.function (Types.list a) b)
          yieldElimination (EliminationList $ inferredTerm rfun) elim [(expected, inferredType rfun)]

        EliminationOptional (OptionalCases n j) -> do
          dom <- freshName
          cod <- freshName
          rn <- infer n
          rj <- infer j
          let t = TypeLambda $ LambdaType dom $ Types.function (Types.optional $ TypeVariable dom) (TypeVariable cod)
          let constraints = inferredConstraints rn ++ inferredConstraints rj
                              ++ [(TypeVariable cod, inferredType rn),
                                  (Types.function (TypeVariable dom) (TypeVariable cod), inferredType rj)]
          yieldElimination (EliminationOptional $ OptionalCases (inferredTerm rn) (inferredTerm rj)) t constraints

        EliminationProduct (TupleProjection arity idx) -> do
          types <- CM.replicateM arity freshTypeVariable
          let cod = types !! idx
          let t = Types.function (Types.product types) cod
          yieldElimination (EliminationProduct $ TupleProjection arity idx) t []

        EliminationRecord (Projection name fname) -> do
          rt <- requireRecordType True name
          sfield <- findMatchingField fname (rowTypeFields rt)
          yieldElimination (EliminationRecord $ Projection name fname)
            (Types.function (TypeRecord rt) $ fieldTypeType sfield) []

        EliminationUnion (CaseStatement tname def cases) -> do
            cod <- freshTypeVariable

            -- Union type
            rt <- requireUnionType True tname
            checkCaseNames tname def cases $ rowTypeFields rt

            -- Default value
            rdef <- case def of
              Nothing -> pure Nothing
              Just d -> Just <$> infer d

            -- Cases
            rcases <- CM.mapM inferFieldType cases
            let pairMap = productOfMaps (M.fromList rcases) (fieldTypeMap $ rowTypeFields rt)

            let defConstraints = Y.maybe [] (\d -> [(cod, inferredType d)]) rdef
            let codConstraints = (\(d, s) -> (inferredType d, Types.function s cod)) <$> M.elems pairMap
            let subtermConstraints = L.concat (inferredConstraints . snd <$> rcases)
            let constraints = defConstraints ++ codConstraints ++ subtermConstraints
            yieldElimination (EliminationUnion (CaseStatement tname (inferredTerm <$> rdef) (inferredToField <$> rcases)))
              (Types.function (TypeUnion rt) cod)
              constraints
          where
            productOfMaps ml mr = M.fromList $ Y.catMaybes (toPair <$> M.toList mr)
              where
                toPair (k, vr) = (\vl -> (k, (vl, vr))) <$> M.lookup k ml
            checkCaseNames tname def cases fields = do
                checkCasesAreSufficient
                checkCasesAreNotSuperfluous
              where
                caseNames = S.fromList (fieldName <$> cases)
                fieldNames = S.fromList (fieldTypeName <$> fields)
                checkCasesAreSufficient = if S.null diff || Y.isJust def
                    then pure ()
                    else fail $ "cases(s) missing with respect to variant of type " ++ unName tname ++ ": "
                      ++ L.intercalate ", " (unFieldName <$> S.toList diff)
                  where
                    diff = S.difference fieldNames caseNames
                checkCasesAreNotSuperfluous = if S.null diff
                    then pure ()
                    else fail $ "case(s) in case statement which do not exist in type " ++ unName tname ++ ": "
                      ++ L.intercalate ", " (unFieldName <$> S.toList diff)
                  where
                    diff = S.difference caseNames fieldNames

        EliminationWrap name -> do
          typ <- requireWrappedType name
          yieldElimination (EliminationWrap name) (Types.function (TypeWrap $ Nominal name typ) typ) []

      FunctionLambda (Lambda v body) -> do
        vdom <- freshName
        let dom = TypeVariable vdom
        rbody <- withBinding v dom $ infer body
        let cod = inferredType rbody
        yieldFunction (FunctionLambda $ Lambda v $ inferredTerm rbody)
          (TypeLambda $ LambdaType vdom $ Types.function dom cod)
          (inferredConstraints rbody)

      FunctionPrimitive name -> do
          t <- typeOfPrimitive name >>= replaceFreeVariables
          yieldFunction (FunctionPrimitive name) t []
        where
          -- This prevents type variables from being reused across multiple instantiations of a primitive within a single element,
          -- which would lead to false unification.
          replaceFreeVariables t = do
              pairs <- CM.mapM toPair $ S.toList $ boundVariablesInType t -- freeVariablesInType t
              return $ substituteTypeVariables (M.fromList pairs) t
            where
              toPair v = do
                v' <- freshTypeVariable
                return (v, v')

    TermLet lt -> inferLet lt

    TermList els -> do
        v <- freshName
        if L.null els
          then yieldTerm (TermList []) (TypeLambda $ LambdaType v $ TypeList $ TypeVariable v) []
          else do
            rels <- CM.mapM infer els
            let co = (\e -> (TypeVariable v, inferredType e)) <$> rels
            let ci = L.concat (inferredConstraints <$> rels)
            yieldTerm (TermList (inferredTerm <$> rels)) (Types.list $ TypeVariable v) (co ++ ci)

    TermLiteral l -> yieldTerm (TermLiteral l) (Types.literal $ literalType l) []

    TermMap m -> do
        kv <- freshName
        vv <- freshName
        if M.null m
          then yieldTerm (TermMap M.empty) (TypeLambda $ LambdaType kv $ TypeLambda $ LambdaType vv
            $ Types.map (TypeVariable kv) (TypeVariable vv)) []
          else do
            pairs <- CM.mapM toPair $ M.toList m
            let co = L.concat ((\(k, v) -> [(TypeVariable kv, inferredType k), (TypeVariable vv, inferredType v)]) <$> pairs)
            let ci = L.concat ((\(k, v) -> inferredConstraints k ++ inferredConstraints v) <$> pairs)
            yieldTerm (TermMap $ M.fromList (fromPair <$> pairs)) (Types.map (TypeVariable kv) (TypeVariable vv)) (co ++ ci)
      where
        fromPair (k, v) = (inferredTerm k, inferredTerm v)
        toPair (k, v) = do
          rk <- infer k
          rv <- infer v
          return (rk, rv)

    TermOptional m -> do
      v <- freshName
      case m of
        Nothing -> yieldTerm (TermOptional Nothing) (TypeLambda $ LambdaType v $ TypeOptional $ TypeVariable v) []
        Just e -> do
          re <- infer e
          let constraints = ((TypeVariable v, inferredType re):(inferredConstraints re))
          yieldTerm
            (TermOptional $ Just $ inferredTerm re)
            (Types.optional $ TypeVariable v)
            constraints

    TermProduct tuple -> do
      rtuple <- CM.mapM infer tuple
      yieldTerm
        (TermProduct (inferredTerm <$> rtuple))
        (TypeProduct (inferredType <$> rtuple))
        (L.concat (inferredConstraints <$> rtuple))

    TermRecord (Record n fields) -> do
        rt <- requireRecordType True n

        rfields <- CM.mapM inferFieldType fields
        let ci = L.concat (inferredConstraints . snd <$> rfields)
        let irt = TypeRecord $ RowType n Nothing (inferredToFieldType <$> rfields)
        yieldTerm (TermRecord $ Record n (inferredToField <$> rfields)) irt ((TypeRecord rt, irt):ci)

    TermSet els -> do
      v <- freshName
      if S.null els
        then yieldTerm (TermSet S.empty) (TypeLambda $ LambdaType v $ Types.set $ TypeVariable v) []
        else do
          rels <- CM.mapM infer $ S.toList els
          let co = (\e -> (TypeVariable v, inferredType e)) <$> rels
          let ci = L.concat (inferredConstraints <$> rels)
          yieldTerm (TermSet $ S.fromList (inferredTerm <$> rels)) (Types.set $ TypeVariable v) (co ++ ci)

    TermSum (Sum i s trm) -> do
        rtrm <- infer trm
        vot <- CM.sequence (varOrTerm rtrm <$> [0..(s-1)])
        let types = fst <$> vot
        let vars = Y.catMaybes (snd <$> vot)
        let typ = L.foldl (\t v -> TypeLambda $ LambdaType v t) (TypeSum types) vars
        yieldTerm (TermSum $ Sum i s $ inferredTerm rtrm) typ (inferredConstraints rtrm)
      where
        varOrTerm rtrm j = if i == j
          then pure (inferredType rtrm, Nothing)
          else do
            v <- freshName
            return (TypeVariable v, Just v)

    TermUnion (Injection n field) -> do
        rt <- requireUnionType True n
        sfield <- findMatchingField (fieldName field) (rowTypeFields rt)

        rfield <- inferFieldType field
        let ci = inferredConstraints $ snd rfield
        let co = (inferredType $ snd rfield, fieldTypeType sfield)

        yieldTerm (TermUnion $ Injection n $ inferredToField rfield) (TypeUnion rt) (co:ci)

    TermVariable v -> do
      t <- requireName v
      yieldTerm (TermVariable v) t []

    TermWrap (Nominal name term1) -> do
      typ <- requireWrappedType name
      rterm1 <- infer term1
      yieldTerm
        (TermWrap $ Nominal name $ inferredTerm rterm1)
        (TypeWrap $ Nominal name typ)
        (inferredConstraints rterm1 ++ [(typ, inferredType rterm1)])

inferElementType :: Element Kv -> Flow (Graph Kv) (Name, Inferred Kv)
inferElementType el = withTrace ("infer type of " ++ unName (elementName el)) $ do
  rterm <- infer $ elementData el
  return (elementName el, rterm)

inferFieldType :: Field Kv -> Flow (Graph Kv) (FieldName, Inferred Kv)
inferFieldType (Field fname term) = do
  rterm <- infer term
  return (fname, rterm)

inferGraphTypes :: Flow (Graph Kv) (Graph Kv)
inferGraphTypes = getState >>= annotateGraph
  where
    annotateGraph g = withTrace ("infer graph types") $ do
        sorted <- sortGraphElements g
        els <- sortGraphElements g >>= annotateElements g
        return g {graphElements = M.fromList (toPair <$> els)}
      where
        toPair el = (elementName el, el)

inferLet :: Let Kv -> Flow (Graph Kv) (Inferred Kv)
inferLet (Let bindings env) = do
    state0 <- getState
    e <- preExtendEnv bindings $ graphTypes state0
    let state1 = state0 {graphTypes = e}
    withState state1 $ do
      -- TODO: perform a topological sort on these bindings; this process should be unified with that of elements in a graph
      let bl = M.toList bindings

      -- Infer types of bindings in the pre-extended environment
      rvalues <- CM.mapM infer (snd <$> bl)
      let rbindings = M.fromList (L.zip (fst <$> bl) (inferredTerm <$> rvalues))
      let bc = L.concat (inferredConstraints <$> rvalues)

      let tbindings = M.fromList (L.zip (fst <$> bl) (inferredType <$> rvalues))
      renv <- withBindings tbindings $ infer env

      yieldTerm
        (TermLet $ Let rbindings $ inferredTerm renv)
        (inferredType renv)
        (bc ++ inferredConstraints renv)
  where
    -- Add any manual type annotations for the bindings to the environment, enabling type inference over recursive definitions
    preExtendEnv bindings e = CM.foldM addPair e $ M.toList bindings
      where
        addPair e (name, term) = do
          mtyp <- annotatedType term
          return $ case mtyp of
            Nothing -> e
            Just typ -> M.insert name typ e
          where
            annotatedType term = do
              anns <- graphAnnotations <$> getState
              annotationClassTypeOf anns $ annotationClassTermAnnotation anns term

-- TODO: deprecated; inference is performed on graphs, not individual terms. Update the Haskell coder to use inferElementType
inferType :: Term -> Flow (Graph Kv) (Type Kv)
--inferType term = (simplifyUniversalTypes . termType) <$> inferTypeAndConstraints term
inferType term = do
  term1 <- inferTypeAndConstraints term
  anns <- graphAnnotations <$> getState
  mtyp <- annotationClassTermType anns term1
  return $ Y.fromJust mtyp

-- TODO: deprecated; inference is performed on graphs, not individual terms. Update tests to use inferElementType
-- | Solve for the top-level type of an expression in a given environment
inferTypeAndConstraints :: Term -> Flow (Graph Kv) (Term)
inferTypeAndConstraints term = withTrace ("infer type") $ initializeGraph $ do
    rterm <- infer term
    subst <- withSchemaContext $ solveConstraints (inferredConstraints rterm)
    anns <- graphAnnotations <$> getState
    substituteAndNormalizeAnnotations anns subst $ inferredTerm rterm

inferredToField (fname, inferred) = Field fname $ inferredTerm inferred
inferredToFieldType (fname, inferred) = FieldType fname $ inferredType inferred

initializeGraph flow = do
    g <- getState
    env <- initialEnv g $ graphAnnotations g
    withState (g {graphTypes = env}) flow
  where
    initialEnv g anns = M.fromList . Y.catMaybes <$> (CM.mapM toPair $ M.elems $ graphElements g)
      where
        toPair el = do
          mt <- annotationClassTermType anns $ elementData el
          return $ (\t -> (elementName el, t)) <$> mt

instantiate :: Type Kv -> Flow (Graph Kv) (Type Kv)
instantiate typ = case typ of
  TypeAnnotated (Annotated typ1 ann) -> TypeAnnotated <$> (Annotated <$> instantiate typ1 <*> pure ann)
  TypeLambda (LambdaType var body) -> do
    var1 <- freshName
    body1 <- substituteTypeVariable var (TypeVariable var1) <$> instantiate body
    return $ TypeLambda $ LambdaType var1 body1
  _ -> pure typ

normalizeType :: Type Kv -> Type Kv
normalizeType = rewriteType f id
  where
    f recurse typ = yank $ recurse typ
      where
        yank typ = case typ of
          TypeAnnotated (Annotated typ1 ann) -> normalize typ1 $ \typ2 -> TypeAnnotated $ Annotated typ2 ann
          TypeApplication (ApplicationType lhs rhs) -> normalize lhs $ \lhs1 ->
            normalize rhs $ \rhs1 -> case lhs of
              TypeLambda (LambdaType var body) -> alphaConvertType var rhs1 body
              _ -> TypeApplication $ ApplicationType lhs1 rhs1
          TypeFunction (FunctionType dom cod) -> normalize dom $
            \dom1 -> normalize cod $
            \cod1 -> TypeFunction $ FunctionType dom1 cod1
          TypeList lt -> normalize lt TypeList
          TypeMap (MapType kt vt) -> normalize kt (\kt1 -> normalize vt (\vt1 -> TypeMap $ MapType kt1 vt1))
          TypeOptional ot -> normalize ot TypeOptional
          TypeProduct types -> case types of
            [] -> TypeProduct []
            (h:rest) -> normalize h
              $ \h1 -> normalize (yank $ TypeProduct rest)
                $ \(TypeProduct rest2) -> TypeProduct $ h1:rest2
          TypeRecord (RowType tname ext fields) -> case fields of
            [] -> TypeRecord (RowType tname ext [])
            ((FieldType fname h):rest) -> normalize h $ \h1 -> normalize (yank $ TypeRecord (RowType tname ext rest))
              $ \(TypeRecord (RowType _ _ rest2)) -> TypeRecord $ RowType tname ext ((FieldType fname h1):rest2)
          TypeSet st -> normalize st TypeSet
          TypeStream st -> normalize st TypeStream
          TypeSum types -> case types of
            [] -> TypeSum []
            (h:rest) -> normalize h $ \h1 -> normalize (yank $ TypeSum rest) $ \(TypeSum rest2) -> TypeSum $ h1:rest2
          TypeUnion (RowType tname ext fields) -> case fields of
            [] -> TypeUnion (RowType tname ext [])
            ((FieldType fname h):rest) -> normalize h $ \h1 -> normalize (yank $ TypeUnion (RowType tname ext rest))
              $ \(TypeUnion (RowType _ _ rest2)) -> TypeUnion $ RowType tname ext ((FieldType fname h1):rest2)
          TypeWrap (Nominal name t) -> normalize t (TypeWrap . Nominal name)
          t -> t
        normalize subtype build = case subtype of
          TypeLambda (LambdaType var body) -> TypeLambda $ LambdaType var $ yank $ build body
          t -> build t

reduceType :: Type Kv -> Type Kv
reduceType t = t -- betaReduceType cx t

requireName :: Name -> Flow (Graph Kv) (Type Kv)
requireName v = do
  env <- graphTypes <$> getState
  case M.lookup v env of
    Nothing -> fail $ "variable not bound in environment: " ++ unName v ++ ". Environment: "
      ++ L.intercalate ", " (unName <$> M.keys env)
    Just s  -> instantiate s

sortGraphElements :: Graph Kv -> Flow (Graph Kv) [Element Kv]
sortGraphElements g = do
    annotated <- S.fromList . Y.catMaybes <$> (CM.mapM ifAnnotated $ M.elems els)
    adjList <- CM.mapM (toAdj annotated) $ M.elems els
    case topologicalSort adjList of
      Left comps -> fail $ "cyclical dependency not resolved through annotations: " ++ L.intercalate ", " (unName <$> L.head comps)
      Right names -> return $ Y.catMaybes ((\n -> M.lookup n els) <$> names)
  where
    els = graphElements g
    ifAnnotated el = do
      mtyp <- annotationClassTermType (graphAnnotations g) $ elementData el
      return $ case mtyp of
        Nothing -> Nothing
        Just _ -> Just $ elementName el
    toAdj annotated el = do
        let deps = L.filter isNotAnnotated $ L.filter isElName $ S.toList $ freeVariablesInTerm $ elementData el

        return (elementName el, deps)
      where
        -- Ignore free variables which are not valid element references
        isElName name = M.member name els
        -- No need for an inference dependency on an element which is already annotated with a type
        isNotAnnotated name = not $ S.member name annotated

substituteAndNormalizeAnnotations :: AnnotationClass Kv -> Subst Kv -> Term -> Flow (Graph Kv) (Term)
substituteAndNormalizeAnnotations anns subst = rewriteTermMetaM rewrite
  where
    -- Note: normalizing each annotation separately results in different variable names for corresponding types
--    rewrite (x, typ, c) = (x, normalizeTypeVariables $ normalizeType $ substituteTypeVariables subst typ, c) -- TODO: restore this
    rewrite ann = do
      mtyp <- annotationClassTypeOf anns ann
      let ntyp = (normalizeType . substituteTypeVariables subst) <$> mtyp
      return $ annotationClassSetTypeOf anns ntyp ann
--    rewrite (x, typ, c) = (x, normalizeType $ substituteTypeVariables subst typ, c)
--    rewrite (x, typ, c) = (x, normalizeType $ substituteTypeVariables subst typ, c)

typeOfPrimitive :: Name -> Flow (Graph Kv) (Type Kv)
typeOfPrimitive name = primitiveType <$> requirePrimitive name

withBinding :: Name -> Type Kv -> Flow (Graph Kv) x -> Flow (Graph Kv) x
withBinding n t = withEnvironment (M.insert n t)

withBindings :: M.Map Name (Type Kv) -> Flow (Graph Kv) x -> Flow (Graph Kv) x
withBindings bindings = withEnvironment (\e -> M.union bindings e)

withEnvironment :: (M.Map Name (Type Kv) -> M.Map Name (Type Kv)) -> Flow (Graph Kv) x -> Flow (Graph Kv) x
withEnvironment m flow = do
  g <- getState
  withState (g {graphTypes = m $ graphTypes g}) flow

yieldFunction :: Function Kv -> Type Kv -> [Constraint Kv] -> Flow (Graph Kv) (Inferred Kv)
yieldFunction fun = yieldTerm (TermFunction fun)

yieldElimination :: Elimination Kv -> Type Kv -> [Constraint Kv] -> Flow (Graph Kv) (Inferred Kv)
yieldElimination e = yieldTerm (TermFunction $ FunctionElimination e)

yieldTerm :: Term -> Type Kv -> [Constraint Kv] -> Flow (Graph Kv) (Inferred Kv)
yieldTerm term typ constraints = do
  g <- getState
  -- For now, we simply annotate each and every subterm, except annotation terms.
  -- In the future, we might choose only to annotate certain subterms as needed, e.g. function terms
  let annTerm = case term of
        TermAnnotated _ -> term
        _ -> annotationClassSetTermType (graphAnnotations g) (Just typ) term
  return $ Inferred annTerm typ constraints
