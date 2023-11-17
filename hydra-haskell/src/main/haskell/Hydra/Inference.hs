-- | Entry point for Hydra type inference, which is a variation on on Hindley-Milner

module Hydra.Inference (
  inferGraphTypes,
  inferTermType,
  inferredTypeOf
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
import Hydra.Rewriting
import Hydra.Strip
import Hydra.Substitution
import Hydra.Coders
import Hydra.Schemas
import Hydra.Tier1
import Hydra.Tier2
import Hydra.Tools.Debug
import Hydra.Tools.Sorting
import Hydra.Unification
import Hydra.Lib.Io -- For debugging

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

findMatchingField :: FieldName -> [FieldType] -> Flow Graph FieldType
findMatchingField fname sfields = case L.filter (\f -> fieldTypeName f == fname) sfields of
  []    -> fail $ "no such field: " ++ unFieldName fname
  (h:_) -> return h

-- Infer the type of a term, without also unifying or normalizing types; the latter is done separately
infer :: Term -> Flow Graph Inferred
infer term = case term of
    TermAnnotated (Annotated subj ann) -> do
      rsubj <- infer subj

      -- If the subject is annotated with a type, unify that type with the inferred type for the subject.
      otyp <- getType ann
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

    TermFunction f -> inferFunctionType f

    TermLet lt -> inferLetType lt

    TermList els -> do
        v <- freshName
        if L.null els
          then return $ yieldTerm (TermList []) (TypeList $ TypeVariable v) []
          else do
            rels <- CM.mapM infer els
            let co = (\e -> (TypeVariable v, inferredType e)) <$> rels
            let ci = L.concat (inferredConstraints <$> rels)
            let typ = TypeList $ TypeVariable v
            return $ yieldTerm (TermList (inferredTerm <$> rels)) typ (co ++ ci)

    TermLiteral l -> return $ yieldTerm (TermLiteral l) (Types.literal $ literalType l) []

    TermMap m -> do
        kv <- freshName
        vv <- freshName
        if M.null m
          then return $ yieldTerm (TermMap M.empty) (Types.map (TypeVariable kv) (TypeVariable vv)) []
          else do
            pairs <- CM.mapM toPair $ M.toList m
            let co = L.concat ((\(k, v) -> [(TypeVariable kv, inferredType k), (TypeVariable vv, inferredType v)]) <$> pairs)
            let ci = L.concat ((\(k, v) -> inferredConstraints k ++ inferredConstraints v) <$> pairs)
            let typ = Types.map (TypeVariable kv) (TypeVariable vv)
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
        Nothing -> return $ yieldTerm (TermOptional Nothing) (TypeOptional $ TypeVariable v) []
        Just e -> do
          re <- infer e
          let constraints = ((TypeVariable v, inferredType re):(inferredConstraints re))
          let typ = TypeOptional $ TypeVariable v
          return $ yieldTerm (TermOptional $ Just $ inferredTerm re) typ constraints

    TermProduct tuple -> do
      rtuple <- CM.mapM infer tuple
      return $ yieldTerm
        (TermProduct (inferredTerm <$> rtuple))
        (TypeProduct (inferredType <$> rtuple))
        (L.concat (inferredConstraints <$> rtuple))

    TermRecord (Record tname fields) -> do
        refType <- withSchemaContext $ requireType tname
        rt <- toRecordType tname refType

        rfields <- CM.mapM inferFieldType fields
        let ci = L.concat (inferredConstraints . snd <$> rfields)
        let irt = TypeRecord $ RowType tname Nothing (inferredToFieldType <$> rfields)

        let term = TermRecord $ Record tname (inferredToField <$> rfields)
--        let typ = irt
        let typ = toApplicationType tname refType
        let constraints = ((TypeRecord rt, irt):ci)
        return $ yieldTerm term typ constraints

    TermSet els -> do
      v <- freshName
      if S.null els
        then return $ yieldTerm (TermSet S.empty) (Types.set $ TypeVariable v) []
        else do
          rels <- CM.mapM infer $ S.toList els
          let co = (\e -> (TypeVariable v, inferredType e)) <$> rels
          let ci = L.concat (inferredConstraints <$> rels)
          let typ = Types.set $ TypeVariable v
          return $ yieldTerm (TermSet $ S.fromList (inferredTerm <$> rels)) typ (co ++ ci)

    TermSum (Sum i s trm) -> do
        rtrm <- infer trm
        vot <- CM.sequence (varOrTerm rtrm <$> [0..(s-1)])
        let types = fst <$> vot
        let typ = TypeSum types
        return $ yieldTerm (TermSum $ Sum i s $ inferredTerm rtrm) typ (inferredConstraints rtrm)
      where
        varOrTerm rtrm j = if i == j
          then pure (inferredType rtrm, Nothing)
          else do
            v <- freshName
            return (TypeVariable v, Just v)

    TermUnion (Injection tname field) -> do
        refType <- withSchemaContext $ requireType tname
        rt <- toUnionType tname refType
        sfield <- findMatchingField (fieldName field) (rowTypeFields rt)

        rfield <- inferFieldType field

        let ci = inferredConstraints $ snd rfield
        let co = (inferredType $ snd rfield, fieldTypeType sfield)
        let constraints = (co:ci)

        let term = TermUnion $ Injection tname $ inferredToField rfield
--        let typ = TypeUnion rt
        let typ = toApplicationType tname refType
        return $ yieldTerm term typ constraints

    TermVariable v -> do
      t <- requireTypeByName v
      return $ yieldTerm (TermVariable v) t []

    TermWrap (Nominal tname term1) -> do
      refType <- withSchemaContext $ requireType tname
      wt <- toWrappedType tname refType
      rterm1 <- infer term1

      let term = TermWrap $ Nominal tname $ inferredTerm rterm1
--      let typ = TypeWrap $ Nominal tname wt
      let typ = toApplicationType tname refType
      let constraints = inferredConstraints rterm1 ++ [(wt, inferredType rterm1)]
      return $ yieldTerm term typ constraints

inferElementType :: Element -> Flow Graph (Name, Inferred)
inferElementType el = withTrace ("infer type of " ++ unName (elementName el)) $ do
  rterm <- infer $ elementData el
  return (elementName el, rterm)

inferElementTypes :: Graph -> [Element] -> Flow Graph [Element]
inferElementTypes g sortedEls = initializeGraph $ inferAll sortedEls [] >>= CM.mapM rewriteElement
  where
    -- Note: inference occurs over the entire graph at once,
    --       but unification and substitution occur within elements in isolation
    rewriteElement (name, rel) = withTrace ("rewrite " ++ unName name) $ do
      term <- normalizeInferredTypes rel
      return $ Element name term

    -- Perform inference on elements in the given order, respecting dependencies among elements
    inferAll before after = case before of
      [] -> pure $ L.reverse after
      (el:rest) -> do
        rel <- inferElementType el
        withBinding (fst rel) (inferredType $ snd rel) $ inferAll rest (rel:after)

inferEliminationType :: Elimination -> Flow Graph Inferred
inferEliminationType e = case e of
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
      let typ = Types.function (Types.optional $ TypeVariable dom) (TypeVariable cod)
      let constraints = inferredConstraints rn ++ inferredConstraints rj
                          ++ [(TypeVariable cod, inferredType rn),
                              (Types.function (TypeVariable dom) (TypeVariable cod), inferredType rj)]
      return $ yieldElimination (EliminationOptional $ OptionalCases (inferredTerm rn) (inferredTerm rj)) typ constraints

    EliminationProduct (TupleProjection arity idx) -> do
      types <- CM.replicateM arity freshTypeVariable
      let cod = types !! idx
      let t = Types.function (Types.product types) cod
      return $ yieldElimination (EliminationProduct $ TupleProjection arity idx) t []

    EliminationRecord (Projection tname fname) -> do
      refType <- withSchemaContext $ requireType tname
      rt <- toRecordType tname refType
      
      sfield <- findMatchingField fname (rowTypeFields rt)
      let elim = EliminationRecord $ Projection tname fname
--      let typ = Types.function (TypeRecord rt) $ fieldTypeType sfield
      let typ = Types.function (toApplicationType tname refType) $ fieldTypeType sfield
      return $ yieldElimination elim typ []

    EliminationUnion (CaseStatement tname def cases) -> do
        cod <- freshTypeVariable

        -- Union type
        refType <- withSchemaContext $ requireType tname
        rt <- toUnionType tname refType
--        fail $ "rt: " ++ show rt
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
        let elim = EliminationUnion (CaseStatement tname (inferredTerm <$> rdef) (inferredToField <$> rcases))
--        let typ = Types.function (TypeUnion rt) cod
        let typ = Types.function (toApplicationType tname refType) cod
        return $ yieldElimination elim typ constraints
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

    EliminationWrap tname -> do
      refType <- withSchemaContext $ requireType tname
      wt <- toWrappedType tname refType
      let elim = EliminationWrap tname
--      let typ = Types.function (TypeWrap $ Nominal tname wt) wt
      let typ = Types.function (toApplicationType tname refType) wt
      return $ yieldElimination elim typ []

inferFieldType :: Field -> Flow Graph (FieldName, Inferred)
inferFieldType (Field fname term) = do
  rterm <- infer term
  return (fname, rterm)

inferFunctionType :: Function -> Flow Graph Inferred
inferFunctionType f = case f of
  FunctionElimination e -> inferEliminationType e

  FunctionLambda (Lambda v body) -> do
    vdom <- freshName
    rbody <- withBinding v (TypeVariable vdom) $ infer body
    let typ = Types.function (TypeVariable vdom) (inferredType rbody)
    return $ yieldFunction (FunctionLambda $ Lambda v $ inferredTerm rbody) typ (inferredConstraints rbody)

  FunctionPrimitive name -> do
      t <- requirePrimitiveType name
      return $ yieldFunction (FunctionPrimitive name) (stripUniversalTypes t) []
    where
      stripUniversalTypes = rewriteType $ \recurse typ -> case recurse typ of
        TypeLambda (LambdaType v body) -> body
        t -> t

inferGraphTypes :: Flow Graph Graph
inferGraphTypes = getState >>= annotateGraph
  where
    annotateGraph g = withTrace ("infer graph types") $ do
        sorted <- sortGraphElements g
--        fail $ "head: " ++ showTerm (elementData $ L.head sorted)
        els <- sortGraphElements g >>= inferElementTypes g
        return g {graphElements = M.fromList (toPair <$> els)}
      where
        toPair el = (elementName el, el)

inferLetType :: Let -> Flow Graph Inferred
inferLetType (Let bindings env) = do
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

-- | Add inferred type annotations to a single term, considered as a standalone graph
inferTermType :: Term -> Flow Graph Term
inferTermType term = withTrace ("infer type") $ initializeGraph $
  infer term >>= normalizeInferredTypes

inferredToField (fname, inferred) = Field fname $ inferredTerm inferred
inferredToFieldType (fname, inferred) = FieldType fname $ inferredType inferred

-- | Find the inferred type of a single term, considered as a standalone graph. Mainly useful in tests.
inferredTypeOf :: Term -> Flow Graph Type
inferredTypeOf term = inferTermType term >>= requireAnnotatedType

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

-- | Get the free type variables of a term in order of occurrence in the annotations of the term and its subterms
--   (following a pre-order traversal in subterms, and in each type expression)
normalFreeVariables :: Term -> Flow Graph [Name]
normalFreeVariables term = L.nub <$> foldOverTermM TraversalOrderPre fld [] term
  where
    fld freeVars term = do
      mtyp <- getAnnotatedType term
      return $ case mtyp of
        Nothing -> freeVars
        Just typ -> freeVars ++ freeVariablesInTypeOrdered typ

normalizeInferredTypes :: Inferred -> Flow Graph Term
normalizeInferredTypes inf = do
    subst <- solveConstraints $ inferredConstraints inf
--    fail $ "subst: " ++ show subst
    g <- getState
    term1 <- pure (inferredTerm inf)
      >>= replacePreunificationVariables subst
      >>= replaceTemporaryVariables
      >>= rewriteTermAnnotationsM (createUniversalTypes g)
--    fail $ "normalized term: " ++ showTerm term1
    return term1
  where
    rewrite subst ann = do
      mtyp <- getType ann
      return $ setType (substituteTypeVariables subst <$> mtyp) ann
    replacePreunificationVariables subst term = do
      term1 <- rewriteTermAnnotationsM (rewrite subst) term
--      fail $ "term: " ++ showTerm term1
      return term1
    replaceTemporaryVariables term = do
      tempVars <- (L.filter isTemporaryVariable) <$> normalFreeVariables term
      let subst = M.fromList $ L.zip tempVars (TypeVariable <$> normalVariables)
      rewriteTermAnnotationsM (rewrite subst) term
    createUniversalTypes g ann = do
        mtyp <- getType ann
        return $ setType (helper <$> mtyp) ann
      where
        helper typ = L.foldl (\t v -> TypeLambda $ LambdaType v t) typ $ L.reverse (freeVars L.\\ typeNames)
          where
            freeVars = freeVariablesInTypeOrdered typ
        typeNames = case graphSchema g of
          Nothing -> []
          Just s -> M.keys $ graphElements s

requireAnnotatedType :: Term -> Flow Graph Type
requireAnnotatedType term = do
  mtyp <- getAnnotatedType term
  case mtyp of
    Nothing -> fail $ "expected an inferred type annotation"
    Just typ -> return typ

requireTypeByName :: Name -> Flow Graph Type
requireTypeByName v = do
  env <- graphTypes <$> getState
  case M.lookup v env of
    Nothing -> fail $ "variable not bound in graph schema: " ++ unName v ++ ". Schema: "
      ++ L.intercalate ", " (unName <$> M.keys env)
    Just s -> pure s -- instantiate s

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

-- | Expands a type reference like "Pair" to an application type like (Pair a b) using fresh type variables,
--   depending on whether "Pair" resolves to a forall type like forall a b. record_Pair{fst: a, snd: b}
toApplicationType :: Name -> Type -> Type
toApplicationType name typ = L.foldl
    (\lhs v -> TypeApplication $ ApplicationType lhs $ TypeVariable v)
    (TypeVariable name) $ L.reverse vars
  where
    vars = forallVars typ
    -- Note: does not dereference unbound variables
    forallVars t = case stripType t of
      TypeApplication (ApplicationType lhs _) -> L.drop 1 $ forallVars lhs
      TypeLambda (LambdaType v body) -> (v:(forallVars body))
      _ -> []

withBinding :: Name -> Type -> Flow Graph a -> Flow Graph a
withBinding n t = withEnvironment (M.insert n t)

withBindings :: M.Map Name Type -> Flow Graph a -> Flow Graph a
withBindings bindings = withEnvironment (\e -> M.union bindings e)

withEnvironment :: (M.Map Name Type -> M.Map Name Type) -> Flow Graph a -> Flow Graph a
withEnvironment m flow = do
  g <- getState
  withState (g {graphTypes = m $ graphTypes g}) flow

yieldElimination :: Elimination -> Type -> [Constraint] -> Inferred
yieldElimination = yieldTerm . TermFunction . FunctionElimination

yieldFunction :: Function -> Type -> [Constraint] -> Inferred
yieldFunction = yieldTerm . TermFunction

yieldTerm :: Term -> Type -> [Constraint] -> Inferred
yieldTerm term typ = Inferred annTerm typ
  where
    -- For now, we simply annotate each and every subterm, except annotation terms.
    -- In the future, we might choose only to annotate certain subterms as needed, e.g. function terms
    annTerm = case term of
      TermAnnotated _ -> term
      _ -> setTermType (Just typ) term
