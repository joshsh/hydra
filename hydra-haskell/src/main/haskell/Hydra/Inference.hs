-- | Entry point for Hydra type inference, which is a variation on on Hindley-Milner

module Hydra.Inference (
  annotateTermWithTypes,
  inferGraphTypes,
  inferType
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


data Inferred = Inferred {
  -- The original term, possibly annotated with the inferred type
  inferredTerm :: Term,
  -- The inferred type
  inferredType :: Type,
  -- Any constraints introduced by the inference process
  inferredConstraints :: [Constraint]
} deriving Show

-- TODO: deprecated; inference is performed on graphs, not individual terms. Update tests to use inferElementType
-- | Solve for the top-level type of an expression in a given environment
annotateTermWithTypes :: Term -> Flow Graph Term
annotateTermWithTypes term = withTrace ("infer type") $ initializeGraph $
  infer term >>= normalizeInferredTypes

findMatchingField :: FieldName -> [FieldType] -> Flow Graph FieldType
findMatchingField fname sfields = case L.filter (\f -> fieldTypeName f == fname) sfields of
  []    -> fail $ "no such field: " ++ unFieldName fname
  (h:_) -> return h

freshName :: Flow Graph Name
freshName = normalVariable <$> nextCount "hyInf"

freshTypeVariable :: Flow Graph Type
freshTypeVariable = TypeVariable <$> freshName

-- Infer the type of a term, without also unifying or normalizing types; this is done separately
infer :: Term -> Flow Graph Inferred
infer term = case term of
    TermAnnotated (Annotated subj ann) -> do
      rsubj <- infer subj
      otyp <- getAnnotatedType term
      let constraints = (inferredConstraints rsubj) ++ case otyp of
            Nothing -> []
            Just t -> [(inferredType rsubj, t)]

      return $ yieldTerm (TermAnnotated $ Annotated (inferredTerm rsubj) ann) (inferredType rsubj) constraints

    TermApplication (Application fun arg) -> do
      rfun <- infer fun
      rarg <- infer arg
      cod <- freshTypeVariable
      let constraints = (inferredConstraints rfun) ++ (inferredConstraints rarg)
            ++ [(inferredType rfun, Types.function (inferredType rarg) cod)]
      return $ yieldTerm (TermApplication $ Application (inferredTerm rfun) (inferredTerm rarg)) cod constraints

    TermFunction f -> inferFunction f

    TermLet lt -> inferLet lt

    TermList els -> do
        v <- freshName
        if L.null els
          then return $ yieldTerm (TermList []) (TypeLambda $ LambdaType v $ TypeList $ TypeVariable v) []
          else do
            rels <- CM.mapM infer els
            let co = (\e -> (TypeVariable v, inferredType e)) <$> rels
            let ci = L.concat (inferredConstraints <$> rels)
            let typ = TypeLambda $ LambdaType v $ TypeList $ TypeVariable v
            return $ yieldTerm (TermList (inferredTerm <$> rels)) typ (co ++ ci)

    TermLiteral l -> return $ yieldTerm (TermLiteral l) (Types.literal $ literalType l) []

    TermMap m -> do
        kv <- freshName
        vv <- freshName
        if M.null m
          then return $ yieldTerm (TermMap M.empty) (TypeLambda $ LambdaType kv $ TypeLambda $ LambdaType vv
            $ Types.map (TypeVariable kv) (TypeVariable vv)) []
          else do
            pairs <- CM.mapM toPair $ M.toList m
            let co = L.concat ((\(k, v) -> [(TypeVariable kv, inferredType k), (TypeVariable vv, inferredType v)]) <$> pairs)
            let ci = L.concat ((\(k, v) -> inferredConstraints k ++ inferredConstraints v) <$> pairs)
            let typ = TypeLambda $ LambdaType kv $ TypeLambda $ LambdaType vv $ Types.map (TypeVariable kv) (TypeVariable vv)
            return $ yieldTerm (TermMap $ M.fromList (fromPair <$> pairs)) typ (co ++ ci)
      where
        fromPair (k, v) = (inferredTerm k, inferredTerm v)
        toPair (k, v) = do
          rk <- infer k
          rv <- infer v
          return (rk, rv)

    TermOptional m -> do
      v <- freshName
      case m of
        Nothing -> return $ yieldTerm (TermOptional Nothing) (TypeLambda $ LambdaType v $ TypeOptional $ TypeVariable v) []
        Just e -> do
          re <- infer e
          let constraints = ((TypeVariable v, inferredType re):(inferredConstraints re))
          let typ = TypeLambda $ LambdaType v $ TypeOptional $ TypeVariable v
          return $ yieldTerm (TermOptional $ Just $ inferredTerm re) typ constraints

    TermProduct tuple -> do
      rtuple <- CM.mapM infer tuple
      return $ yieldTerm
        (TermProduct (inferredTerm <$> rtuple))
        (TypeProduct (inferredType <$> rtuple))
        (L.concat (inferredConstraints <$> rtuple))

    TermRecord (Record n fields) -> do
        rt <- requireRecordType True n

        rfields <- CM.mapM inferFieldType fields
        let ci = L.concat (inferredConstraints . snd <$> rfields)
        let irt = TypeRecord $ RowType n Nothing (inferredToFieldType <$> rfields)
        return $ yieldTerm (TermRecord $ Record n (inferredToField <$> rfields)) irt ((TypeRecord rt, irt):ci)

    TermSet els -> do
      v <- freshName
      if S.null els
        then return $ yieldTerm (TermSet S.empty) (TypeLambda $ LambdaType v $ Types.set $ TypeVariable v) []
        else do
          rels <- CM.mapM infer $ S.toList els
          let co = (\e -> (TypeVariable v, inferredType e)) <$> rels
          let ci = L.concat (inferredConstraints <$> rels)
          let typ = TypeLambda $ LambdaType v $ Types.set $ TypeVariable v
          return $ yieldTerm (TermSet $ S.fromList (inferredTerm <$> rels)) typ (co ++ ci)

    TermSum (Sum i s trm) -> do
        rtrm <- infer trm
        vot <- CM.sequence (varOrTerm rtrm <$> [0..(s-1)])
        let types = fst <$> vot
        let vars = Y.catMaybes (snd <$> vot)
        let typ = L.foldl (\t v -> TypeLambda $ LambdaType v t) (TypeSum types) vars
        return $ yieldTerm (TermSum $ Sum i s $ inferredTerm rtrm) typ (inferredConstraints rtrm)
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

        return $ yieldTerm (TermUnion $ Injection n $ inferredToField rfield) (TypeUnion rt) (co:ci)

    TermVariable v -> do
      t <- requireName v
      return $ yieldTerm (TermVariable v) t []

    TermWrap (Nominal name term1) -> do
      typ <- requireWrappedType name
      rterm1 <- infer term1
      return $ yieldTerm
        (TermWrap $ Nominal name $ inferredTerm rterm1)
        (TypeWrap $ Nominal name typ)
        (inferredConstraints rterm1 ++ [(typ, inferredType rterm1)])

inferElementType :: Element -> Flow Graph (Name, Inferred)
inferElementType el = withTrace ("infer type of " ++ unName (elementName el)) $ do
  rterm <- infer $ elementData el
  return (elementName el, rterm)

inferElementTypes :: Graph -> [Element] -> Flow Graph [Element]
inferElementTypes g sortedEls = initializeGraph $ inferAll sortedEls [] >>= CM.mapM rewriteElement
  where
    -- Note: inference occurs over the entire graph at once,
    --       but unification and substitution occur within elements in isolation
    rewriteElement (name, rel) = do
      term <- normalizeInferredTypes rel
      return $ Element name term

    -- Perform inference on elements in the given order, respecting dependencies among elements
    inferAll before after = case before of
      [] -> pure $ L.reverse after
      (el:rest) -> do
        rel <- inferElementType el
        withBinding (fst rel) (inferredType $ snd rel) $ inferAll rest (rel:after)

inferElimination :: Elimination -> Flow Graph Inferred
inferElimination e = case e of
    EliminationList fun -> do
      a <- freshTypeVariable
      b <- freshTypeVariable
      let expected = Types.function b (Types.function a b)
      rfun <- infer fun
      let elim = Types.function b (Types.function (Types.list a) b)
      return $ yieldElimination (EliminationList $ inferredTerm rfun) elim [(expected, inferredType rfun)]

    EliminationOptional (OptionalCases n j) -> do
      dom <- freshName
      cod <- freshName
      rn <- infer n
      rj <- infer j
      let t = TypeLambda $ LambdaType dom $ Types.function (Types.optional $ TypeVariable dom) (TypeVariable cod)
      let constraints = inferredConstraints rn ++ inferredConstraints rj
                          ++ [(TypeVariable cod, inferredType rn),
                              (Types.function (TypeVariable dom) (TypeVariable cod), inferredType rj)]
      return $ yieldElimination (EliminationOptional $ OptionalCases (inferredTerm rn) (inferredTerm rj)) t constraints

    EliminationProduct (TupleProjection arity idx) -> do
      types <- CM.replicateM arity freshTypeVariable
      let cod = types !! idx
      let t = Types.function (Types.product types) cod
      return $ yieldElimination (EliminationProduct $ TupleProjection arity idx) t []

    EliminationRecord (Projection name fname) -> do
      rt <- requireRecordType True name
      sfield <- findMatchingField fname (rowTypeFields rt)
      return $ yieldElimination (EliminationRecord $ Projection name fname)
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
        return $ yieldElimination (EliminationUnion (CaseStatement tname (inferredTerm <$> rdef) (inferredToField <$> rcases)))
          (Types.function (TypeUnion rt) cod)
          --(Types.function (TypeVariable tname) cod)
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
      return $ yieldElimination (EliminationWrap name) (Types.function (TypeWrap $ Nominal name typ) typ) []

inferFieldType :: Field -> Flow Graph (FieldName, Inferred)
inferFieldType (Field fname term) = do
  rterm <- infer term
  return (fname, rterm)

inferFunction :: Function -> Flow Graph Inferred
inferFunction f = case f of
  FunctionElimination e -> inferElimination e

  FunctionLambda (Lambda v body) -> do
    vdom <- freshName
    let dom = TypeVariable vdom
    rbody <- withBinding v dom $ infer body
    let cod = inferredType rbody
    return $ yieldFunction (FunctionLambda $ Lambda v $ inferredTerm rbody)
      (TypeLambda $ LambdaType vdom $ Types.function dom cod)
      (inferredConstraints rbody)

  FunctionPrimitive name -> do
      -- Replacing variables prevents type variables from being reused across multiple instantiations of a primitive within a single element,
      -- which would lead to false unification.
      t <- typeOfPrimitive name >>= replaceBoundTypeVariables

      return $ yieldFunction (FunctionPrimitive name) t []

inferGraphTypes :: Flow Graph Graph
inferGraphTypes = getState >>= annotateGraph
  where
    annotateGraph g = withTrace ("infer graph types") $ do
        sorted <- sortGraphElements g
        els <- sortGraphElements g >>= inferElementTypes g
        return g {graphElements = M.fromList (toPair <$> els)}
      where
        toPair el = (elementName el, el)

inferLet :: Let -> Flow Graph Inferred
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

      return $ yieldTerm
        (TermLet $ Let rbindings $ inferredTerm renv)
        (inferredType renv)
        (bc ++ inferredConstraints renv)
  where
    -- Add any manual type annotations for the bindings to the environment, enabling type inference over recursive definitions
    preExtendEnv bindings e = CM.foldM addPair e $ M.toList bindings
      where
        addPair e (name, term) = do
          mtyp <- getAnnotatedType term
          return $ case mtyp of
            Nothing -> e
            Just typ -> M.insert name typ e

-- TODO: deprecated; inference is performed on graphs, not individual terms. Update the Haskell coder to use inferElementType
inferType :: Term -> Flow Graph Type
inferType term = annotateTermWithTypes term >>= requireAnnotatedType

inferredToField (fname, inferred) = Field fname $ inferredTerm inferred
inferredToFieldType (fname, inferred) = FieldType fname $ inferredType inferred

initializeGraph flow = do
    g <- getState
    env <- initialEnv g
    withState (g {graphTypes = env}) flow
  where
    initialEnv g = M.fromList . Y.catMaybes <$> (CM.mapM toPair $ M.elems $ graphElements g)
      where
        toPair el = do
          mt <- getAnnotatedType $ elementData el
          return $ (\t -> (elementName el, t)) <$> mt

instantiate :: Type -> Flow Graph Type
instantiate typ = case typ of
  TypeAnnotated (Annotated typ1 ann) -> TypeAnnotated <$> (Annotated <$> instantiate typ1 <*> pure ann)
  TypeLambda (LambdaType var body) -> do
    var1 <- freshName
    body1 <- substituteTypeVariable var (TypeVariable var1) <$> instantiate body
    return $ TypeLambda $ LambdaType var1 body1
  _ -> pure typ

normalizeInferredTypes :: Inferred -> Flow Graph Term
normalizeInferredTypes inf = do
    subst <- withSchemaContext $ solveConstraints $ inferredConstraints inf
    -- TODO: consider combining these two rewriting steps
    rewriteTermAnnotationsM (rewrite subst) (inferredTerm inf) >>= normalizeVariables
  where
    rewrite subst ann = do
      mtyp <- getType ann
      let ntyp = (normalizePolytypes . substituteTypeVariables subst) <$> mtyp
      return $ setType ntyp ann
    normalizeVariables term = do
        -- Note: the inferred type is not rewritten and is no longer meaningful; only the type annotations are rewritten
        typ <- requireAnnotatedType term
        -- The substitution is derived from the top-level type annotation only,
        -- but for consistency, the same substitution is also applied to the type annotations of subterms
        -- We make the assumption that any type variables bound in subterm annotations are the same as the type
        -- variables bound in the top-level annotation.
        let subst = M.fromList $ L.zip (boundTypeVariablesOf typ) normalVariables
        rewriteTypeAnnotationsOnTerms (replaceTypeVariables subst) term

replaceBoundTypeVariables :: Type -> Flow Graph Type
replaceBoundTypeVariables t = do
    pairs <- CM.mapM toPair $ boundTypeVariablesOf t
    return $ replaceTypeVariables (M.fromList pairs) t
  where
    toPair v = do
      v' <- freshName
      return (v, v')

replaceTypeVariables :: M.Map Name Name -> Type -> Type
replaceTypeVariables subst = rewriteType $ \recurse t -> case recurse t of
  TypeVariable v -> case M.lookup v subst of
    Nothing -> t
    Just v1 -> TypeVariable v1
  TypeLambda (LambdaType v body) -> case M.lookup v subst of
    Nothing -> t
    Just v1 -> TypeLambda $ LambdaType v1 body
  t1 -> t1

requireName :: Name -> Flow Graph Type
requireName v = do
  env <- graphTypes <$> getState
  case M.lookup v env of
    Nothing -> fail $ "variable not bound in environment: " ++ unName v ++ ". Environment: "
      ++ L.intercalate ", " (unName <$> M.keys env)
    Just s -> instantiate s

requireAnnotatedType :: Term -> Flow Graph Type
requireAnnotatedType term = do
  mtyp <- getAnnotatedType term
  case mtyp of
    Nothing -> fail $ "expected an inferred type annotation"
    Just typ -> return typ

rewriteTypeAnnotationsOnTerms :: (Type -> Type) -> Term -> Flow Graph Term
rewriteTypeAnnotationsOnTerms f = rewriteTermM mapExpr
  where
    mapExpr recurse term = case term of
      TermAnnotated (Annotated term1 ann) -> do
        mtyp <- getType ann
        case mtyp of
          Nothing -> TermAnnotated <$> (Annotated <$> recurse term1 <*> pure ann)
          Just typ -> TermAnnotated <$> (Annotated <$> recurse term1 <*> pure (setType (Just $ f typ) ann))
      _ -> recurse term

sortGraphElements :: Graph -> Flow Graph [Element]
sortGraphElements g = do
    annotated <- S.fromList . Y.catMaybes <$> (CM.mapM ifAnnotated $ M.elems els)
    let adjList = (toAdj annotated) <$> M.elems els
    case topologicalSort adjList of
      Left comps -> fail $ "cyclical dependency not resolved through annotations: " ++ L.intercalate ", " (unName <$> L.head comps)
      Right names -> return $ Y.catMaybes ((\n -> M.lookup n els) <$> names)
  where
    els = graphElements g
    ifAnnotated el = do
      mtyp <- getAnnotatedType $ elementData el
      return $ case mtyp of
        Nothing -> Nothing
        Just _ -> Just $ elementName el
    toAdj annotated el = (elementName el, deps)
      where
        deps = L.filter isNotAnnotated $ L.filter isElName $ S.toList $ freeVariablesInTerm $ elementData el
        -- Ignore free variables which are not valid element references
        isElName name = M.member name els
        -- No need for an inference dependency on an element which is already annotated with a type
        isNotAnnotated name = not $ S.member name annotated

typeOfPrimitive :: Name -> Flow Graph Type
typeOfPrimitive name = primitiveType <$> requirePrimitive name

withBinding :: Name -> Type -> Flow Graph a -> Flow Graph a
withBinding n t = withEnvironment (M.insert n t)

withBindings :: M.Map Name Type -> Flow Graph a -> Flow Graph a
withBindings bindings = withEnvironment (\e -> M.union bindings e)

withEnvironment :: (M.Map Name Type -> M.Map Name Type) -> Flow Graph a -> Flow Graph a
withEnvironment m flow = do
  g <- getState
  withState (g {graphTypes = m $ graphTypes g}) flow

yieldFunction :: Function -> Type -> [Constraint] -> Inferred
yieldFunction fun = yieldTerm (TermFunction fun)

yieldElimination :: Elimination -> Type -> [Constraint] -> Inferred
yieldElimination e = yieldTerm (TermFunction $ FunctionElimination e)

yieldTerm :: Term -> Type -> [Constraint] -> Inferred
yieldTerm term typ constraints = Inferred annTerm typ constraints
  where
    -- For now, we simply annotate each and every subterm, except annotation terms.
    -- In the future, we might choose only to annotate certain subterms as needed, e.g. function terms
    annTerm = case term of
      TermAnnotated _ -> term
      _ -> setTermType (Just typ) term
