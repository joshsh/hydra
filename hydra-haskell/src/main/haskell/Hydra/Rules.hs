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


type InfAnn a = (a, Type a, [Constraint a])

data InferenceContext a = InferenceContext {
  inferenceContextGraph :: Graph a,
  inferenceContextEnvironment :: TypingEnvironment a}

type TypingEnvironment a = M.Map Name (Type a)

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

fieldType :: Field (InfAnn a) -> FieldType a
fieldType (Field fname term) = FieldType fname $ termType term

findMatchingField :: Show a => FieldName -> [FieldType a] -> Flow (InferenceContext a) (FieldType a)
findMatchingField fname sfields = case L.filter (\f -> fieldTypeName f == fname) sfields of
  []    -> fail $ "no such field: " ++ unFieldName fname
  (h:_) -> return h

freshName :: Flow (InferenceContext a) Name
freshName = normalVariable <$> nextCount "hyInf"

freshTypeVariable :: Flow (InferenceContext a) (Type a)
freshTypeVariable = TypeVariable <$> freshName

--generalize :: Show a => TypingEnvironment a -> Type a -> Type a
--generalize env t  = L.foldl (\body n -> TypeLambda $ LambdaType n body) t vars
--  where
--    vars = S.toList $ S.difference -- TODO: preserve order
--      (freeVariablesInType t)
--      (L.foldr (S.union . freeVariablesInType) S.empty $ M.elems env)

infer :: (Eq a, Ord a, Show a) => Term a -> Flow (InferenceContext a) (Term (InfAnn a))
infer term = withTrace ("infer for " ++ show (termVariant term)) $ case term of
    TermAnnotated (Annotated term1 ann) -> do
      iterm <- infer term1
      anns <- graphAnnotations . inferenceContextGraph <$> getState
      otyp <- withGraphContext $ annotationClassTermType anns term
      return $ case iterm of
        -- `yield` produces the default annotation, which can just be replaced
        TermAnnotated (Annotated trm (_, t, c)) -> TermAnnotated (Annotated trm (ann, t, infEqAnn ++ c))
          where
            infEqAnn = case otyp of
              Nothing -> []
              Just t' -> [(t, t')]

    TermApplication (Application fun arg) -> do
      ifun <- infer fun
      iarg <- infer arg
      cod <- freshTypeVariable
      let constraints = (termConstraints ifun) ++ (termConstraints iarg) ++ [(termType ifun, Types.function (termType iarg) cod)]
      yield (TermApplication $ Application ifun iarg) cod constraints

    TermFunction f -> case f of

      FunctionElimination e -> case e of

        EliminationList fun -> do
          a <- freshTypeVariable
          b <- freshTypeVariable
          let expected = Types.function b (Types.function a b)
          i <- infer fun
          let elim = Types.function b (Types.function (Types.list a) b)
          yieldElimination (EliminationList i) elim [(expected, termType i)]

        EliminationOptional (OptionalCases n j) -> do
          dom <- freshName
          cod <- freshName
          ni <- infer n
          ji <- infer j
          let t = TypeLambda $ LambdaType dom $ Types.function (Types.optional $ TypeVariable dom) (TypeVariable cod)
          let constraints = termConstraints ni ++ termConstraints ji
                              ++ [(TypeVariable cod, termType ni), (Types.function (TypeVariable dom) (TypeVariable cod), termType ji)]
          yieldElimination (EliminationOptional $ OptionalCases ni ji) t constraints

        EliminationProduct (TupleProjection arity idx) -> do
          types <- CM.replicateM arity freshTypeVariable
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
                idf <- infer d
                return (Just idf, termConstraints idf)

            -- Cases
            icases <- CM.mapM inferFieldType cases
            let icasesMap = fieldMap icases
            rt <- withGraphContext $ requireUnionType True tname
            let sfields = fieldTypeMap  $ rowTypeFields rt
            checkCasesAgainstSchema tname icasesMap sfields
            let pairMap = productOfMaps icasesMap sfields

            cod <- freshTypeVariable
            let outerConstraints = (\(d, s) -> (termType d, Types.function s cod)) <$> M.elems pairMap
            let innerConstraints = dfltConstraints ++ L.concat (termConstraints <$> M.elems icasesMap)

            yieldElimination (EliminationUnion (CaseStatement tname idef icases))
              (Types.function (TypeUnion rt) cod)
              (innerConstraints ++ outerConstraints)
          where
            checkCasesAgainstSchema tname icases sfields = if M.null diff
                then pure ()
                else fail $ "case(s) in case statement which do not exist in type " ++ unName tname ++ ": "
                  ++ L.intercalate ", " (unFieldName <$> M.keys diff)
              where
                diff = M.difference icases sfields

        EliminationWrap name -> do
          typ <- withGraphContext $ requireWrappedType name
          yieldElimination (EliminationWrap name) (Types.function (TypeWrap $ Nominal name typ) typ) []

      FunctionLambda (Lambda v body) -> do
        vdom <- freshName
        let dom = TypeVariable vdom
        i <- withBinding v dom $ infer body
        let cod = termType i
        yieldFunction (FunctionLambda $ Lambda v i)
          (TypeLambda $ LambdaType vdom $ Types.function dom cod)
--          (Types.function dom cod)
          (termConstraints i)

      FunctionPrimitive name -> do
          t <- (withGraphContext $ typeOfPrimitive name) >>= replaceFreeVariables
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
          then yield (TermList []) (TypeLambda $ LambdaType v $ TypeList $ TypeVariable v) []
          else do
            iels <- CM.mapM infer els
            let co = (\e -> (TypeVariable v, termType e)) <$> iels
            let ci = L.concat (termConstraints <$> iels)
            yield (TermList iels) (Types.list $ TypeVariable v) (co ++ ci)

    TermLiteral l -> yield (TermLiteral l) (Types.literal $ literalType l) []

    TermMap m -> do
        kv <- freshName
        vv <- freshName
        if M.null m
          then yield (TermMap M.empty) (TypeLambda $ LambdaType kv $ TypeLambda $ LambdaType vv
            $ Types.map (TypeVariable kv) (TypeVariable vv)) []
          else do
            pairs <- CM.mapM toPair $ M.toList m
            let co = L.concat ((\(k, v) -> [(TypeVariable kv, termType k), (TypeVariable vv, termType v)]) <$> pairs)
            let ci = L.concat ((\(k, v) -> termConstraints k ++ termConstraints v) <$> pairs)
            yield (TermMap $ M.fromList pairs) (Types.map (TypeVariable kv) (TypeVariable vv)) (co ++ ci)
      where
        toPair (k, v) = do
          ik <- infer k
          iv <- infer v
          return (ik, iv)

    TermOptional m -> do
      v <- freshName
      case m of
        Nothing -> yield (TermOptional Nothing) (TypeLambda $ LambdaType v $ TypeOptional $ TypeVariable v) []
        Just e -> do
          i <- infer e
          let ci = termConstraints i
          yield (TermOptional $ Just i) (Types.optional $ TypeVariable v) ((TypeVariable v, termType i):ci)

    TermProduct tuple -> do
      is <- CM.mapM infer tuple
      yield (TermProduct is) (TypeProduct $ fmap termType is) (L.concat $ fmap termConstraints is)

    TermRecord (Record n fields) -> do
        rt <- withGraphContext $ requireRecordType True n
        ifields <- CM.mapM inferFieldType fields
        let ci = L.concat (termConstraints . fieldTerm <$> ifields)
        let irt = TypeRecord $ RowType n Nothing (fieldType <$> ifields)
        yield (TermRecord $ Record n ifields) irt ((TypeRecord rt, irt):ci)

    TermSet els -> do
      v <- freshName
      if S.null els
        then yield (TermSet S.empty) (TypeLambda $ LambdaType v $ Types.set $ TypeVariable v) []
        else do
          iels <- CM.mapM infer $ S.toList els
          let co = (\e -> (TypeVariable v, termType e)) <$> iels
          let ci = L.concat (termConstraints <$> iels)
          yield (TermSet $ S.fromList iels) (Types.set $ TypeVariable v) (co ++ ci)

    TermSum (Sum i s trm) -> do
        it <- infer trm
        vot <- CM.sequence (varOrTerm it <$> [0..(s-1)])
        let types = fst <$> vot
        let vars = Y.catMaybes (snd <$> vot)
        let typ = L.foldl (\t v -> TypeLambda $ LambdaType v t) (TypeSum types) vars
        yield (TermSum $ Sum i s it) typ (termConstraints it)
      where
        varOrTerm it j = if i == j
          then pure (termType it, Nothing)
          else do
            v <- freshName
            return (TypeVariable v, Just v)

    TermUnion (Injection n field) -> do
        rt <- withGraphContext $ requireUnionType True n
        sfield <- findMatchingField (fieldName field) (rowTypeFields rt)
        ifield <- inferFieldType field
        let ci = termConstraints $ fieldTerm ifield
        let co = (termType $ fieldTerm ifield, fieldTypeType sfield)

        yield (TermUnion $ Injection n ifield) (TypeUnion rt) (co:ci)

    TermVariable v -> do
      t <- requireName v
      yield (TermVariable v) t []

    TermWrap (Nominal name term1) -> do
      typ <- withGraphContext $ requireWrappedType name
      i <- infer term1
      yield (TermWrap $ Nominal name i) (TypeWrap $ Nominal name typ) (termConstraints i ++ [(typ, termType i)])

inferFieldType :: (Ord a, Show a) => Field a -> Flow (InferenceContext a) (Field (InfAnn a))
inferFieldType (Field fname term) = Field fname <$> infer term

inferLet :: (Ord a, Show a) => Let a -> Flow (InferenceContext a) (Term (InfAnn a))
inferLet (Let bindings env) = withTrace ("let(" ++ L.intercalate "," (unName . fst <$> M.toList bindings) ++ ")") $ do
    state0 <- getState
    e <- preExtendEnv bindings $ inferenceContextEnvironment state0
    let state1 = state0 {inferenceContextEnvironment = e}
    withState state1 $ do
      -- TODO: perform a topological sort on these bindings; this process should be unified with that of elements in a graph
      let bl = M.toList bindings

      -- Infer types of bindings in the pre-extended environment
      ivalues <- CM.mapM infer (snd <$> bl)
      let ibindings = M.fromList (L.zip (fst <$> bl) ivalues)
      let bc = L.concat (termConstraints <$> ivalues)

      let tbindings = M.map termType ibindings
      ienv <- withBindings tbindings $ infer env

      yield (TermLet $ Let ibindings ienv) (termType ienv) (bc ++ termConstraints ienv)
  where
    -- Add any manual type annotations for the bindings to the environment, enabling type inference over recursive definitions
    preExtendEnv bindings e = withGraphContext $ CM.foldM addPair e $ M.toList bindings
      where
        addPair e (name, term) = do
          mtyp <- typeOfTerm term
          return $ case mtyp of
            Nothing -> e
            Just typ -> M.insert name typ e

instantiate :: Type a -> Flow (InferenceContext a) (Type a)
instantiate typ = case typ of
  TypeAnnotated (Annotated typ1 ann) -> TypeAnnotated <$> (Annotated <$> instantiate typ1 <*> pure ann)
  TypeLambda (LambdaType var body) -> do
    var1 <- freshName
    body1 <- substituteTypeVariable var (TypeVariable var1) <$> instantiate body
    return $ TypeLambda $ LambdaType var1 body1
  _ -> pure typ

productOfMaps :: Ord k => M.Map k l -> M.Map k r -> M.Map k (l, r)
productOfMaps ml mr = M.fromList $ Y.catMaybes (toPair <$> M.toList mr)
  where
    toPair (k, vr) = (\vl -> (k, (vl, vr))) <$> M.lookup k ml

reduceType :: (Ord a, Show a) => Type a -> Type a
reduceType t = t -- betaReduceType cx t

requireName :: Show a => Name -> Flow (InferenceContext a) (Type a)
requireName v = do
  env <- inferenceContextEnvironment <$> getState
  case M.lookup v env of
    Nothing -> fail $ "variable not bound in environment: " ++ unName v ++ ". Environment: "
      ++ L.intercalate ", " (unName <$> M.keys env)
    Just s  -> instantiate s

termConstraints :: Show a => Term (InfAnn a) -> [Constraint a]
termConstraints term = case term of
  (TermAnnotated (Annotated _ (_, _, constraints))) -> constraints
  _ -> throwDebugException $ "expected an annotated term. Found: " ++ show term

termType :: Term (InfAnn a) -> Type a
termType (TermAnnotated (Annotated _ (_, typ, _))) = typ

typeOfPrimitive :: Name -> Flow (Graph a) (Type a)
typeOfPrimitive name = primitiveType <$> requirePrimitive name

typeOfTerm :: Term a -> Flow (Graph a) (Maybe (Type a))
typeOfTerm term = do
  anns <- graphAnnotations <$> getState
  annotationClassTypeOf anns $ annotationClassTermAnnotation anns term

withBinding :: Name -> Type a -> Flow (InferenceContext a) x -> Flow (InferenceContext a) x
withBinding n t = withEnvironment (M.insert n t)

withBindings :: M.Map Name (Type a) -> Flow (InferenceContext a) x -> Flow (InferenceContext a) x
withBindings bindings = withEnvironment (\e -> M.union bindings e)

withEnvironment :: (TypingEnvironment a -> TypingEnvironment a) -> Flow (InferenceContext a) x -> Flow (InferenceContext a) x
withEnvironment m flow = do
  InferenceContext g e <- getState
  withState (InferenceContext g (m e)) flow

withGraphContext :: Flow (Graph a) x -> Flow (InferenceContext a) x
withGraphContext f = do
  cx <- inferenceContextGraph <$> getState
  withState cx f

yield :: (Eq a, Ord a, Show a) => Term (InfAnn a) -> Type a -> [Constraint a] -> Flow (InferenceContext a) (Term (InfAnn a))
yield term typ constraints = do
  case term of
    TermAnnotated _ -> fail "doubly-annotated term"
    _ -> pure ()
  g <- inferenceContextGraph <$> getState
  let defAnn = annotationClassDefault $ graphAnnotations g
  return $ TermAnnotated $ Annotated term (defAnn, typ, constraints)

yieldFunction :: (Eq a, Ord a, Show a) => Function (InfAnn a) -> Type a -> [Constraint a] -> Flow (InferenceContext a) (Term (InfAnn a))
yieldFunction fun = yield (TermFunction fun)

yieldElimination :: (Eq a, Ord a, Show a) => Elimination (InfAnn a) -> Type a -> [Constraint a] -> Flow (InferenceContext a) (Term (InfAnn a))
yieldElimination e = yield (TermFunction $ FunctionElimination e)
