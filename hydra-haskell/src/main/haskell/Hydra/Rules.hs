-- | Inference rules

module Hydra.Rules where

import Hydra.Basics
import Hydra.Strip
import Hydra.Compute
import Hydra.Core
import Hydra.CoreDecoding
import Hydra.CoreEncoding
import Hydra.Graph
import Hydra.Lexical
import Hydra.Mantle
import Hydra.Reduction
import Hydra.Rewriting
import Hydra.Substitution
import Hydra.Unification
import Hydra.Tools.Debug
import Hydra.Kv
import Hydra.Tier1
import Hydra.Tier2
import qualified Hydra.Dsl.Types as Types

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


data Inferred a = Inferred {
  -- The original term, possibly annotated with the inferred type
  inferredTerm :: Term a,
  -- The inferred type
  inferredType :: Type a,
  -- Any constraints introduced by the inference process
  inferredConstraints :: [Constraint a]
}

-- Decode a type, eliminating nominal types for the sake of unification
decodeStructuralType :: Show a => Term a -> Flow (Graph a) (Type a)
decodeStructuralType term = do
  typ <- coreDecodeType term
  let typ' = stripType typ
  case typ' of
    TypeVariable name -> withSchemaContext $ withTrace "decode structural type" $ do
      el <- requireElement name
      decodeStructuralType $ elementData el
    _ -> pure typ

findMatchingField :: Show a => FieldName -> [FieldType a] -> Flow (Graph a) (FieldType a)
findMatchingField fname sfields = case L.filter (\f -> fieldTypeName f == fname) sfields of
  []    -> fail $ "no such field: " ++ unFieldName fname
  (h:_) -> return h

freshName :: Flow (Graph a) Name
freshName = normalVariable <$> nextCount "hyInf"

freshTypeVariable :: Flow (Graph a) (Type a)
freshTypeVariable = TypeVariable <$> freshName

infer :: (Eq a, Ord a, Show a) => Term a -> Flow (Graph a) (Inferred a)
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

inferFieldType :: (Ord a, Show a) => Field a -> Flow (Graph a) (FieldName, Inferred a)
inferFieldType (Field fname term) = do
  rterm <- infer term
  return (fname, rterm)

inferLet :: (Ord a, Show a) => Let a -> Flow (Graph a) (Inferred a)
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

inferredToField (fname, inferred) = Field fname $ inferredTerm inferred
inferredToFieldType (fname, inferred) = FieldType fname $ inferredType inferred

instantiate :: Type a -> Flow (Graph a) (Type a)
instantiate typ = case typ of
  TypeAnnotated (Annotated typ1 ann) -> TypeAnnotated <$> (Annotated <$> instantiate typ1 <*> pure ann)
  TypeLambda (LambdaType var body) -> do
    var1 <- freshName
    body1 <- substituteTypeVariable var (TypeVariable var1) <$> instantiate body
    return $ TypeLambda $ LambdaType var1 body1
  _ -> pure typ

reduceType :: (Ord a, Show a) => Type a -> Type a
reduceType t = t -- betaReduceType cx t

requireName :: Show a => Name -> Flow (Graph a) (Type a)
requireName v = do
  env <- graphTypes <$> getState
  case M.lookup v env of
    Nothing -> fail $ "variable not bound in environment: " ++ unName v ++ ". Environment: "
      ++ L.intercalate ", " (unName <$> M.keys env)
    Just s  -> instantiate s

typeOfPrimitive :: Name -> Flow (Graph a) (Type a)
typeOfPrimitive name = primitiveType <$> requirePrimitive name

withBinding :: Name -> Type a -> Flow (Graph a) x -> Flow (Graph a) x
withBinding n t = withEnvironment (M.insert n t)

withBindings :: M.Map Name (Type a) -> Flow (Graph a) x -> Flow (Graph a) x
withBindings bindings = withEnvironment (\e -> M.union bindings e)

withEnvironment :: (M.Map Name (Type a) -> M.Map Name (Type a)) -> Flow (Graph a) x -> Flow (Graph a) x
withEnvironment m flow = do
  g <- getState
  withState (g {graphTypes = m $ graphTypes g}) flow

yieldFunction :: (Eq a, Ord a, Show a) => Function a -> Type a -> [Constraint a] -> Flow (Graph a) (Inferred a)
yieldFunction fun = yieldTerm (TermFunction fun)

yieldElimination :: (Eq a, Ord a, Show a) => Elimination a -> Type a -> [Constraint a] -> Flow (Graph a) (Inferred a)
yieldElimination e = yieldTerm (TermFunction $ FunctionElimination e)

yieldTerm :: (Eq a, Ord a, Show a) => Term a -> Type a -> [Constraint a] -> Flow (Graph a) (Inferred a)
yieldTerm term typ constraints = do
  g <- getState
  -- For now, we simply annotate each and every subterm, except annotation terms.
  -- In the future, we might choose only to annotate certain subterms as needed, e.g. function terms
  let annTerm = case term of
        TermAnnotated _ -> term
        _ -> annotationClassSetTermType (graphAnnotations g) (Just typ) term
  return $ Inferred annTerm typ constraints
