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


data InferenceContext = InferenceContext {
  inferenceContextGraph :: Graph,
  inferenceContextEnvironment :: TypingEnvironment}

type TypingEnvironment = M.Map Name TypeScheme

fieldType :: Field -> FieldType
fieldType (Field fname term) = FieldType fname $ termType term

findMatchingField :: Name -> [FieldType] -> Flow InferenceContext (FieldType)
findMatchingField fname sfields = case L.filter (\f -> fieldTypeName f == fname) sfields of
  []    -> fail $ "no such field: " ++ unName fname
  (h:_) -> return h

freshName :: Flow InferenceContext (Type)
freshName = TypeVariable . normalVariable <$> nextCount "hyInf"

generalize :: TypingEnvironment -> Type -> TypeScheme
generalize env t  = TypeScheme vars t
  where
    vars = S.toList $ S.difference
      (freeVariablesInType t)
      (L.foldr (S.union . freeVariablesInScheme) S.empty $ M.elems env)

infer :: Term -> Flow InferenceContext (Term, [Constraint])
infer term = withTrace ("infer for " ++ show (termVariant term)) $ case term of
    TermAnnotated (AnnotatedTerm term1 ann) -> do
      (term2, constraints) <- infer term1
      return (TermAnnotated $ AnnotatedTerm term2 ann, constraints)

    TermTyped (TermWithType term1 typ) -> do
      (i, c) <- infer term1
      return (setTermType (Just typ) i, c ++ [(typ, termType i)])

    TermApplication (Application fun arg) -> do
      (ifun, funconst) <- infer fun
      (iarg, argconst) <- infer arg
      cod <- freshName
      let constraints = funconst ++ argconst ++ [(termType ifun, Types.function (termType iarg) cod)]
      yield (TermApplication $ Application ifun iarg) cod constraints

    TermFunction f -> case f of

      FunctionElimination e -> case e of

        EliminationList fun -> do
          a <- freshName
          b <- freshName
          let expected = Types.functionN [b, a, b]
          (i, c) <- infer fun
          let elim = Types.functionN [b, Types.list a, b]
          yieldElimination (EliminationList i) elim (c ++ [(expected, termType i)])

        EliminationOptional (OptionalCases n j) -> do
          dom <- freshName
          cod <- freshName
          (ni, nconst) <- infer n
          (ji, jconst) <- infer j
          let t = Types.function (Types.optional dom) cod
          let constraints = nconst ++ jconst
                              ++ [(cod, termType ni), (Types.function dom cod, termType ji)]
          yieldElimination (EliminationOptional $ OptionalCases ni ji) t constraints

        EliminationProduct (TupleProjection arity idx) -> do
          types <- CM.replicateM arity freshName
          let cod = types !! idx
          let t = Types.function (Types.product types) cod
          yieldElimination (EliminationProduct $ TupleProjection arity idx) t []

        EliminationRecord (Projection name fname) -> do
          rt <- withGraphContext $ requireRecordType True name
          sfield <- findMatchingField fname (rowTypeFields rt)
          yieldElimination (EliminationRecord $ Projection name fname)
            (Types.function (TypeRecord rt) $ fieldTypeType sfield) []

        EliminationUnion (CaseStatement tname def cases) -> do
            -- Default value
            (idef, dfltConstraints) <- case def of
              Nothing -> pure (Nothing, [])
              Just d -> do
                (i, c) <- infer d
                return (Just i, c)

            -- Cases
            icases' <- CM.mapM inferFieldType cases
            let icases = fst <$> icases'
            let casesconst = snd <$> icases'
            let icasesMap = fieldMap icases
            rt <- withGraphContext $ requireUnionType True tname
            let sfields = fieldTypeMap  $ rowTypeFields rt
            checkCasesAgainstSchema tname icasesMap sfields
            let pairMap = productOfMaps icasesMap sfields

            cod <- freshName
            let outerConstraints = (\(d, s) -> (termType d, Types.function s cod)) <$> M.elems pairMap
            let innerConstraints = dfltConstraints ++ L.concat casesconst

            yieldElimination (EliminationUnion (CaseStatement tname idef icases))
              (Types.function (TypeUnion rt) cod)
              (innerConstraints ++ outerConstraints)
          where
            checkCasesAgainstSchema tname icases sfields = if M.null diff
                then pure ()
                else fail $ "case(s) in case statement which do not exist in type " ++ unName tname ++ ": "
                  ++ L.intercalate ", " (unName <$> M.keys diff)
              where
                diff = M.difference icases sfields

        EliminationWrap name -> do
          typ <- withGraphContext $ requireWrappedType name
          yieldElimination (EliminationWrap name) (Types.function (TypeWrap $ WrappedType name typ) typ) []

      FunctionLambda (Lambda v body) -> do
        tv <- freshName
        (i, iconst) <- withBinding v (monotype tv) $ infer body
        yieldFunction (FunctionLambda $ Lambda v i) (Types.function tv (termType i)) iconst

      FunctionPrimitive name -> do
          t <- (withGraphContext $ typeOfPrimitive name) >>= replaceFreeVariables
          yieldFunction (FunctionPrimitive name) t []
        where
          -- This prevents type variables from being reused across multiple instantiations of a primitive within a single element,
          -- which would lead to false unification.
          replaceFreeVariables t = do
              pairs <- CM.mapM toPair $ S.toList $ freeVariablesInType t
              return $ substituteInType (M.fromList pairs) t
            where
              toPair v = do
                v' <- freshName
                return (v, v')

    TermLet lt -> inferLet lt

    TermList els -> do
        v <- freshName
        if L.null els
          then yield (TermList []) (Types.list v) []
          else do
            iels' <- CM.mapM infer els
            let iels = fst <$> iels'
            let elsconst = snd <$> iels'
            let co = (\e -> (v, termType e)) <$> iels
            let ci = L.concat elsconst
            yield (TermList iels) (Types.list v) (co ++ ci)

    TermLiteral l -> yield (TermLiteral l) (Types.literal $ literalType l) []

    TermMap m -> do
        kv <- freshName
        vv <- freshName
        if M.null m
          then yield (TermMap M.empty) (Types.map kv vv) []
          else do
            triples <- CM.mapM toTriple $ M.toList m
            let pairs = (\(k, v, _) -> (k, v)) <$> triples
            let co = L.concat ((\(k, v, c) -> c ++ [(kv, termType k), (vv, termType v)]) <$> triples)
            yield (TermMap $ M.fromList pairs) (Types.map kv vv) co
      where
        toTriple (k, v) = do
          (ik, kc) <- infer k
          (iv, vc) <- infer v
          return (ik, iv, kc ++ vc)

    TermOptional m -> do
      v <- freshName
      case m of
        Nothing -> yield (TermOptional Nothing) (Types.optional v) []
        Just e -> do
          (i, ci) <- infer e
          yield (TermOptional $ Just i) (Types.optional v) ((v, termType i):ci)

    TermProduct tuple -> do
      is' <- CM.mapM infer tuple
      let is = fst <$> is'
      let co = L.concat (snd <$> is')
      yield (TermProduct is) (TypeProduct $ fmap termType is) co

    TermRecord (Record n fields) -> do
        rt <- withGraphContext $ requireRecordType True n
        ifields' <- CM.mapM inferFieldType fields
        let ifields = fst <$> ifields'
        let ci = L.concat (snd <$> ifields')
        let irt = TypeRecord $ RowType n Nothing (fieldType <$> ifields)
        yield (TermRecord $ Record n ifields) irt ((TypeRecord rt, irt):ci)

    TermSet els -> do
      v <- freshName
      if S.null els
        then yield (TermSet S.empty) (Types.set v) []
        else do
          iels' <- CM.mapM infer $ S.toList els
          let iels = fst <$> iels'
          let co = (\e -> (v, termType e)) <$> iels
          let ci = L.concat (snd <$> iels')
          yield (TermSet $ S.fromList iels) (Types.set v) (co ++ ci)

    TermSum (Sum i s trm) -> do
        (it, co) <- infer trm
        types <- CM.sequence (varOrTerm it <$> [0..(s-1)])
        yield (TermSum $ Sum i s it) (TypeSum types) co
      where
        varOrTerm it j = if i == j
          then pure $ termType it
          else freshName

    TermUnion (Injection n field) -> do
        rt <- withGraphContext $ requireUnionType True n
        sfield <- findMatchingField (fieldName field) (rowTypeFields rt)
        (ifield, ci) <- inferFieldType field
        let co = (termType $ fieldTerm ifield, fieldTypeType sfield)

        yield (TermUnion $ Injection n ifield) (TypeUnion rt) (co:ci)

    TermVariable v -> do
      t <- requireName v
      yield (TermVariable v) t []

    TermWrap (WrappedTerm name term1) -> do
      typ <- withGraphContext $ requireWrappedType name
      (i, ci) <- infer term1
      yield (TermWrap $ WrappedTerm name i) (TypeWrap $ WrappedType name typ) (ci ++ [(typ, termType i)])

inferFieldType :: Field -> Flow InferenceContext (Field, [Constraint])
inferFieldType (Field fname term) = do
  (i, c) <- infer term
  return (Field fname i, c)

inferLet :: Let -> Flow InferenceContext (Term, [Constraint])
inferLet (Let bindings env) = withTrace ("let(" ++ L.intercalate "," (unName . fst <$> M.toList bindings) ++ ")") $ do
    state0 <- getState
    let e = preExtendEnv bindings $ inferenceContextEnvironment state0
    let state1 = state0 {inferenceContextEnvironment = e}
    withState state1 $ do
      -- TODO: perform a topological sort on these bindings; this process should be unified with that of elements in a graph
      let bl = M.toList bindings

      -- Infer types of bindings in the pre-extended environment
      ivalues' <- CM.mapM infer (snd <$> bl)
      let ivalues = fst <$> ivalues'
      let ibindings = M.fromList (L.zip (fst <$> bl) ivalues)
      let bc = L.concat (snd <$> ivalues')

      let tbindings = M.map termTypeScheme ibindings
      (ienv, cenv) <- withBindings tbindings $ infer env

      yield (TermLet $ Let ibindings ienv) (termType ienv) (bc ++ cenv)
  where
    -- Add any manual type annotations for the bindings to the environment, enabling type inference over recursive definitions
    preExtendEnv bindings e = foldl addPair e $ M.toList bindings
      where
        addPair e (name, term) = case typeOfTerm term of
          Nothing -> e
          Just typ -> M.insert name (monotype typ) e

instantiate :: TypeScheme -> Flow InferenceContext (Type)
instantiate (TypeScheme vars t) = do
    vars1 <- mapM (const freshName) vars
    return $ substituteInType (M.fromList $ zip vars vars1) t

monotype :: Type -> TypeScheme
monotype typ = TypeScheme [] typ

productOfMaps :: Ord k => M.Map k l -> M.Map k r -> M.Map k (l, r)
productOfMaps ml mr = M.fromList $ Y.catMaybes (toPair <$> M.toList mr)
  where
    toPair (k, vr) = (\vl -> (k, (vl, vr))) <$> M.lookup k ml

reduceType :: Type -> Type
reduceType t = t -- betaReduceType cx t

requireName :: Name -> Flow InferenceContext (Type)
requireName v = do
  env <- inferenceContextEnvironment <$> getState
  case M.lookup v env of
    Nothing -> fail $ "variable not bound in environment: " ++ unName v ++ ". Environment: "
      ++ L.intercalate ", " (unName <$> M.keys env)
    Just s  -> instantiate s

termType :: Term -> Type
termType term = case stripTerm term of
  (TermTyped (TermWithType _ typ)) -> typ

-- TODO: limited and temporary
termTypeScheme :: Term -> TypeScheme
termTypeScheme = monotype . termType

typeOfPrimitive :: Name -> Flow (Graph) (Type)
typeOfPrimitive name = primitiveType <$> requirePrimitive name

typeOfTerm :: Term -> Maybe Type
typeOfTerm term = case term of
  TermAnnotated (AnnotatedTerm term1 _) -> typeOfTerm term1
  TermTyped (TermWithType term1 typ) -> Just typ
  _ -> Nothing

withBinding :: Name -> TypeScheme -> Flow InferenceContext x -> Flow InferenceContext x
withBinding n ts = withEnvironment (M.insert n ts)

withBindings :: M.Map Name TypeScheme -> Flow InferenceContext x -> Flow InferenceContext x
withBindings bindings = withEnvironment (\e -> M.union bindings e)

withEnvironment :: (TypingEnvironment -> TypingEnvironment) -> Flow InferenceContext x -> Flow InferenceContext x
withEnvironment m flow = do
  InferenceContext g e <- getState
  withState (InferenceContext g (m e)) flow

withGraphContext :: Flow (Graph) x -> Flow InferenceContext x
withGraphContext f = do
  cx <- inferenceContextGraph <$> getState
  withState cx f

yield :: Term -> Type -> [Constraint] -> Flow InferenceContext (Term, [Constraint])
yield term typ constraints = do
  return (TermTyped $ TermWithType term typ, constraints)

yieldFunction :: Function -> Type -> [Constraint] -> Flow InferenceContext (Term, [Constraint])
yieldFunction fun = yield (TermFunction fun)

yieldElimination :: Elimination -> Type -> [Constraint] -> Flow InferenceContext (Term, [Constraint])
yieldElimination e = yield (TermFunction $ FunctionElimination e)
