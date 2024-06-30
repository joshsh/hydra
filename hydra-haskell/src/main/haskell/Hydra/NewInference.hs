module Hydra.NewInference where

import Hydra.Basics
import Hydra.Core
import Hydra.Compute
import Hydra.Mantle
import qualified Hydra.Flows as F
import qualified Hydra.Tier1 as Tier1
import qualified Hydra.Lib.Flows as Flows
import qualified Hydra.Dsl.Types as Types

import qualified Data.List as L
import qualified Data.Map as M


--------------------------------------------------------------------------------
-- Graphs

showType :: Type -> String
showType (TypeFunction (FunctionType dom cod)) = "(" ++ showType dom ++ "→" ++ showType cod ++ ")"
showType (TypeList etyp) = "[" ++ showType etyp ++ "]"
showType (TypeLiteral lit) = show lit
showType (TypeMap (MapType keyTyp valTyp)) = "map<" ++ showType keyTyp ++ "," ++ showType valTyp ++ ">"
showType (TypeProduct types) = "(" ++ (L.intercalate "," (fmap showType types)) ++ ")"
showType (TypeVariable (Name name)) = name

showTypeScheme :: TypeScheme -> String
showTypeScheme (TypeScheme vars body) = "∀[" ++ (L.intercalate "," (fmap (\(Name name) -> name) vars)) ++ "]." ++ showType body

showConstraint :: TypeConstraint -> String
showConstraint (TypeConstraint ltyp rtyp _) = showType ltyp ++ "≡" ++ showType rtyp

--------------------------------------------------------------------------------
-- Unification

type UnificationContext = Maybe String

data SUnificationError
  = SUnificationErrorCannotUnify Type Type UnificationContext
  | SUnificationErrorOccursCheckFailed Name Type UnificationContext
  deriving (Eq, Ord, Show)

sOccursIn :: Name -> Type -> Bool
sOccursIn var typ = case typ of
  TypeFunction (FunctionType domTyp codTyp) -> sOccursIn var domTyp || sOccursIn var codTyp
  TypeList etyp -> sOccursIn var etyp
  TypeLiteral _ -> False
  TypeMap (MapType keyTyp valTyp) -> sOccursIn var keyTyp || sOccursIn var valTyp
  TypeProduct types -> any (sOccursIn var) types
  TypeVariable name -> var == name

----------------------------------------
-- Robinson's algorithm, following https://www.cs.cornell.edu/courses/cs6110/2017sp/lectures/lec23.pdf

uUnify :: [TypeConstraint] -> Either SUnificationError SSubst
uUnify constraints = case constraints of
    [] -> Right sEmptySubst
    ((TypeConstraint t1 t2 ctx):rest) -> case t1 of
        TypeVariable v1 -> case t2 of
          TypeVariable v2 -> if v1 == v2
            then uUnify rest
            else uBind v1 t2
          _ -> uBind v1 t2
        _ -> case t2 of
          TypeVariable v2 -> uBind v2 t1
          _ -> uUnifyOther t1 t2
      where
        -- TODO: this occurs check is expensive; consider delaying it until the time of substitution
        uBind v t = if sOccursIn v t
            then Left $ SUnificationErrorOccursCheckFailed v t ctx
            else case uUnify (L.map (uSubstInConstraint v t) rest) of
              Left err -> Left err
              Right subst -> Right $ SSubst $ M.union (M.singleton v $ sSubstituteTypeVariables subst t) $ sUnSubst subst
        uUnifyOther t1 t2 = case t1 of
            TypeFunction (FunctionType dom1 cod1) -> case t2 of
              TypeFunction (FunctionType dom2 cod2) -> uUnify $ [
                (TypeConstraint dom1 dom2 ctx), (TypeConstraint cod1 cod2 ctx)] ++ rest
              _ -> cannotUnify
            TypeList l1 -> case t2 of
              TypeList l2 -> uUnify $ [(TypeConstraint l1 l2 ctx)] ++ rest
              _ -> cannotUnify
            TypeLiteral lit1 -> case t2 of
              TypeLiteral lit2 -> if lit1 == lit2
                then uUnify rest
                else cannotUnify
              _ -> cannotUnify
            TypeMap (MapType key1 val1) -> case t2 of
              TypeMap (MapType key2 val2) -> uUnify $ [
                (TypeConstraint key1 key2 ctx), (TypeConstraint val1 val2 ctx)] ++ rest
              _ -> cannotUnify
            TypeProduct types1 -> case t2 of
              TypeProduct types2 -> if L.length types1 /= L.length types2
                then cannotUnify
                else uUnify $ L.zipWith (\t1 t2 -> TypeConstraint t1 t2 ctx) types1 types2 ++ rest
              _ -> cannotUnify
          where
            cannotUnify = Left $ SUnificationErrorCannotUnify t1 t2 ctx

-- TODO: substituting one variable at a time is inefficient
uSubst :: Name -> Type -> Type -> Type
uSubst v t typ = case typ of
  TypeFunction (FunctionType dom cod) -> TypeFunction $ FunctionType (uSubst v t dom) (uSubst v t cod)
  TypeList etyp -> TypeList $ uSubst v t etyp
  TypeLiteral _ -> typ
  TypeMap (MapType key val) -> TypeMap $ MapType (uSubst v t key) (uSubst v t val)
  TypeProduct types -> TypeProduct $ fmap (uSubst v t) types
  TypeVariable name -> if name == v then t else typ

uSubstInConstraint :: Name -> Type -> TypeConstraint -> TypeConstraint
uSubstInConstraint v t (TypeConstraint t1 t2 ctx) = TypeConstraint (uSubst v t t1) (uSubst v t t2) ctx

--------------------------------------------------------------------------------
-- Substitution

data SSubst = SSubst { sUnSubst :: M.Map Name Type }

instance Show SSubst where
  show (SSubst subst) = "{" ++ L.intercalate ", " (fmap (\((Name k), v) -> k ++ ": " ++ showType v) $ M.toList subst) ++ "}"

sEmptySubst = SSubst M.empty

sSubstituteTypeVariables :: SSubst -> Type -> Type
sSubstituteTypeVariables subst typ = case typ of
  TypeFunction (FunctionType dom cod) -> TypeFunction $
    FunctionType (sSubstituteTypeVariables subst dom) (sSubstituteTypeVariables subst cod)
  TypeList etyp -> TypeList $ sSubstituteTypeVariables subst etyp
  TypeLiteral _ -> typ
  TypeMap (MapType key val) -> TypeMap $
    MapType (sSubstituteTypeVariables subst key) (sSubstituteTypeVariables subst val)
  TypeProduct types -> TypeProduct $ fmap (sSubstituteTypeVariables subst) types
  TypeVariable name -> case M.lookup name (sUnSubst subst) of
    Just styp -> styp
    Nothing -> typ

-- TODO: remove unused bound type variables
sSubstituteTypeVariablesInScheme :: SSubst -> TypeScheme -> TypeScheme
sSubstituteTypeVariablesInScheme subst (TypeScheme vars typ) = TypeScheme vars $ sSubstituteTypeVariables subst typ


--------------------------------------------------------------------------------
-- Inference

data SInferenceContext
  = SInferenceContext {
    sInferenceContextLexicon :: M.Map Name TypeScheme,
    sInferenceContextVariableCount :: Int,
    sInferenceContextTypingEnvironment :: M.Map Name TypeScheme}
  deriving (Eq, Ord, Show)

data SInferenceResult
  = SInferenceResult {
    sInferenceResultScheme :: TypeScheme,
    sInferenceResultConstraints :: [TypeConstraint]}
  deriving (Eq, Ord)
instance Show SInferenceResult where
  show (SInferenceResult scheme constraints) = "{type= " ++ showTypeScheme scheme ++ ", constraints= " ++ show constraints ++ "}"

sInferType :: Term -> Flow SInferenceContext TypeScheme
sInferType term = Flows.bind (sInferTypeInternal term) unifyAndSubst
  where
    unifyAndSubst :: SInferenceResult -> Flow SInferenceContext TypeScheme
    unifyAndSubst result = Flows.bind (F.fromEither $ uUnify $ sInferenceResultConstraints result) doSubst
      where
        doSubst :: SSubst -> Flow SInferenceContext TypeScheme
        doSubst subst = sInstantiateAndNormalize $ sSubstituteTypeVariablesInScheme subst $ sInferenceResultScheme result

sInferTypeInternal :: Term -> Flow SInferenceContext SInferenceResult
sInferTypeInternal term = case term of

    TermApplication (Application lterm rterm) -> Flows.bind sNewVar withVar1
      where
        withVar1 dom = Flows.bind sNewVar withVar2
          where
            withVar2 cod = Flows.bind (sInferTypeInternal lterm) withLeft
              where
                withLeft lresult = Flows.bind (sInferTypeInternal rterm) withRight
                  where
                    withRight rresult = Flows.pure $ SInferenceResult (TypeScheme tvars $ TypeVariable cod) $ [
                        TypeConstraint (Types.function (TypeVariable dom) (TypeVariable cod)) ltyp ctx,
                        TypeConstraint (TypeVariable dom) rtyp ctx]
                        ++ sInferenceResultConstraints lresult ++ sInferenceResultConstraints rresult
                      where
                        ctx = Just "application"
                        ltyp = typeSchemeType $ sInferenceResultScheme lresult
                        rtyp = typeSchemeType $ sInferenceResultScheme rresult
                        tvars = typeSchemeVariables (sInferenceResultScheme lresult) ++ typeSchemeVariables (sInferenceResultScheme rresult)

    TermFunction (FunctionLambda (Lambda var _ body)) -> Flows.bind sNewVar withVar
     where
        withVar tvar = sWithTypeBinding var (Types.mono $ TypeVariable tvar) $ Flows.map withBodyType (sInferTypeInternal body)
          where
            -- TODO: prove that tvar will never appear in vars
            withBodyType (SInferenceResult (TypeScheme vars t) constraints)
              = SInferenceResult (TypeScheme (tvar:vars) $ Types.function (TypeVariable tvar) t) constraints

    -- TODO: propagate rawValueVars and envVars into the final result, possibly after substitution
    -- TODO: recursive and mutually recursive let
    TermLet (Let fields env) -> if L.length fields > 2
        then sInferTypeInternal $ TermLet (Let [L.head fields] $ TermLet $ Let (L.tail fields) env)
        else forSingleBinding $ L.head fields
      where
        forSingleBinding (Field key value) = Flows.bind sNewVar withVar
          where
            -- Create a temporary type variable for the binding
            withVar var = sWithTypeBinding key (Types.mono $ TypeVariable var) $
                Flows.bind (sInferTypeInternal value) withValueType
              where
                -- Unify and substitute over the value constraints
                -- TODO: save the substitution and pass it along, instead of the original set of constraints
                withValueType (SInferenceResult rawValueScheme valueConstraints) = Flows.bind (F.fromEither $ uUnify kvConstraints) afterUnification
                  where
                    rawValueVars = typeSchemeVariables rawValueScheme
                    kvConstraints = keyConstraint:valueConstraints
                    keyConstraint = TypeConstraint (TypeVariable var) (typeSchemeType rawValueScheme) $ Just "let binding"
                    -- Now update the type binding to use the inferred type
                    afterUnification subst = sWithTypeBinding key valueScheme
                        $ Flows.map withEnvType (sInferTypeInternal env)
                      where
                        valueScheme = sSubstituteTypeVariablesInScheme subst rawValueScheme
                        withEnvType (SInferenceResult envScheme envConstraints) = SInferenceResult envScheme constraints
                          where
                            constraints = kvConstraints ++ envConstraints
                            envVars = typeSchemeVariables envScheme

    TermList els -> Flows.bind sNewVar withVar
      where
        withVar tvar = if L.null els
            then Flows.pure $ yield (TypeScheme [tvar] $ Types.list $ TypeVariable tvar) []
            else Flows.map fromResults (Flows.sequence (sInferTypeInternal <$> els))
          where
            fromResults results = yield (TypeScheme vars $ Types.list $ TypeVariable tvar) constraints
              where
                uctx = Just "list element"
                constraints = cinner ++ couter
                cinner = L.concat (sInferenceResultConstraints <$> results)
                couter = fmap (\t -> TypeConstraint (TypeVariable tvar) t uctx) types
                types = typeSchemeType . sInferenceResultScheme <$> results
                vars = L.concat (typeSchemeVariables . sInferenceResultScheme <$> results)

    TermLiteral lit -> Flows.pure $ yieldWithoutConstraints $ Types.mono $ TypeLiteral $ literalType lit

    TermMap m -> Flows.bind sNewVar withKeyVar
      where
        withKeyVar kvar = Flows.bind sNewVar withValueVar
          where
            withValueVar vvar = if M.null m
               then Flows.pure $ yield (TypeScheme [kvar, vvar] $ Types.map (TypeVariable kvar) (TypeVariable vvar)) []
               else Flows.map withResults (Flows.sequence $ fmap fromPair $ M.toList m)
              where
                fromPair (k, v) = Flows.bind (sInferTypeInternal k) withKeyType
                  where
                    withKeyType (SInferenceResult (TypeScheme kvars kt) kconstraints) = Flows.map withValueType (sInferTypeInternal v)
                      where
                        withValueType (SInferenceResult (TypeScheme vvars vt) vconstraints)
                          = (kvars ++ vvars,
                             [TypeConstraint (TypeVariable kvar) kt $ Just "map key",
                              TypeConstraint (TypeVariable vvar) vt $ Just "map value"]
                              ++ kconstraints ++ vconstraints)
                withResults pairs = yield (TypeScheme (L.concat (fst <$> pairs)) $ Types.map (TypeVariable kvar) (TypeVariable vvar)) $
                  L.concat (snd <$> pairs)

    TermFunction (FunctionPrimitive name) -> Flow $ \ctx t -> case M.lookup name (sInferenceContextLexicon ctx) of
      Just scheme -> unFlow (Flows.map withoutConstraints $ sInstantiate scheme) ctx t
      Nothing -> unFlow (Flows.fail $ "No such primitive: " ++ unName name) ctx t

    TermProduct els -> if L.null els
      then Flows.pure $ yield (Types.mono $ Types.product []) []
      else Flows.map fromResults (Flows.sequence (sInferTypeInternal <$> els))
      where
        fromResults results = yield (TypeScheme tvars $ TypeProduct tbodies) constraints
          where
            tvars = L.concat $ typeSchemeVariables . sInferenceResultScheme <$> results
            tbodies = typeSchemeType . sInferenceResultScheme <$> results
            constraints = L.concat $ sInferenceResultConstraints <$> results

    TermVariable var -> Flow $ \ctx t -> case M.lookup var (sInferenceContextTypingEnvironment ctx) of
      Just scheme -> unFlow (Flows.map withoutConstraints $ sInstantiate scheme) ctx t
      Nothing -> unFlow (Flows.fail $ "Variable not bound to type: " ++ unName var) ctx t

  where
    unsupported = Flows.fail "Not yet supported"
    yield = SInferenceResult
    yieldWithoutConstraints scheme = yield scheme []
    withoutConstraints scheme = SInferenceResult scheme []

sInstantiate :: TypeScheme -> Flow SInferenceContext TypeScheme
sInstantiate scheme = Flows.map doSubst (sNewVars $ L.length oldVars)
    where
      doSubst newVars = TypeScheme newVars $ sSubstituteTypeVariables subst $ typeSchemeType scheme
        where
          subst = SSubst $ M.fromList $ L.zip oldVars (TypeVariable <$> newVars)
      oldVars = L.intersect (L.nub $ typeSchemeVariables scheme) (sFreeTypeVariables $ typeSchemeType scheme)

sInstantiateAndNormalize :: TypeScheme -> Flow SInferenceContext TypeScheme
sInstantiateAndNormalize scheme = Flows.map sNormalizeTypeVariables (sInstantiate scheme)

sFreeTypeVariables :: Type -> [Name]
sFreeTypeVariables typ = case typ of
  TypeFunction (FunctionType dom cod) -> L.nub $ sFreeTypeVariables dom ++ sFreeTypeVariables cod
  TypeList t -> sFreeTypeVariables t
  TypeLiteral _ -> []
  TypeMap (MapType k v) -> L.nub $ sFreeTypeVariables k ++ sFreeTypeVariables v
  TypeProduct types -> L.nub $ L.concat $ sFreeTypeVariables <$> types
  TypeVariable name -> [name]

sNormalizeTypeVariables :: TypeScheme -> TypeScheme
sNormalizeTypeVariables scheme = TypeScheme newVars $ sSubstituteTypeVariables subst $ typeSchemeType scheme
  where
    normalVariables = (\n -> Name $ "t" ++ show n) <$> [0..]
    oldVars = typeSchemeVariables scheme
    newVars = L.take (L.length oldVars) normalVariables
    subst =SSubst $ M.fromList $ L.zip oldVars (TypeVariable <$> newVars)

sNewVar :: Flow SInferenceContext Name
sNewVar = Flows.map L.head (sNewVars 1)

sNewVars :: Int -> Flow SInferenceContext [Name]
sNewVars n = Flow helper
  where
    helper ctx t = FlowState value ctx' t
      where
        value = Just ((\n -> Name $ "t" ++ show n) <$> (L.take n [(sInferenceContextVariableCount ctx)..]))
        ctx' = ctx {sInferenceContextVariableCount = n + sInferenceContextVariableCount ctx}

sVarScheme :: Name -> TypeScheme
sVarScheme v = TypeScheme [v] $ TypeVariable v

-- | Temporarily add a (term variable, type scheme) to the typing environment
sWithTypeBinding :: Name -> TypeScheme -> Flow SInferenceContext a -> Flow SInferenceContext a
sWithTypeBinding name scheme f = Flow helper
  where
    helper ctx0 t0 = FlowState e ctx3 t1
      where
        env = sInferenceContextTypingEnvironment ctx0
        ctx1 = ctx0 {sInferenceContextTypingEnvironment = M.insert name scheme env}
        FlowState e ctx2 t1 = unFlow f ctx1 t0
        ctx3 = ctx2 {sInferenceContextTypingEnvironment = env}


--------------------------------------------------------------------------------
-- Testing

_app l r = TermApplication $ Application l r
_int = TermLiteral . LiteralInteger . IntegerValueInt32
_lambda v b = TermFunction $ FunctionLambda $ Lambda (Name v) Nothing b
_list = TermList
_map = TermMap
_pair l r = TermProduct [l, r]
_str = TermLiteral . LiteralString
_var = TermVariable . Name

(@@) :: Term -> Term -> Term
f @@ x = TermApplication $ Application f x

infixr 0 >:
(>:) :: String -> Term -> (Name, Term)
n >: t = (Name n, t)

int32 = TermLiteral . LiteralInteger . IntegerValueInt32
lambda v b = TermFunction $ FunctionLambda $ Lambda (Name v) Nothing b
list = TermList
map = TermMap
pair l r = TermProduct [l, r]
string = TermLiteral . LiteralString
var = TermVariable . Name
with env bindings = L.foldl (\e (k, v) -> TermLet $ Let [Field k v] e) env bindings




infixr 0 ===
(===) :: Type -> Type -> TypeConstraint
t1 === t2 = TypeConstraint t1 t2 $ Just "some context"


_add = TermFunction $ FunctionPrimitive $ Name "add"
primPred = TermFunction $ FunctionPrimitive $ Name "primPred"
primSucc = TermFunction $ FunctionPrimitive $ Name "primSucc"

_unify t1 t2 = uUnify [TypeConstraint t1 t2 $ Just "ctx"]

sTestLexicon = M.fromList [
  (Name "add", Types.mono $ Types.function Types.int32 Types.int32),
  (Name "primPred", Types.mono $ Types.function Types.int32 Types.int32),
  (Name "primSucc", Types.mono $ Types.function Types.int32 Types.int32)]

sInitialContext = SInferenceContext sTestLexicon 0 M.empty

_infer term = flowStateValue $ unFlow (sInferType term) sInitialContext Tier1.emptyTrace

_inferRaw term = flowStateValue $ unFlow (sInferTypeInternal term) sInitialContext Tier1.emptyTrace

_instantiate scheme = flowStateValue $ unFlow (sInstantiate scheme) sInitialContext Tier1.emptyTrace

_con t1 t2 = TypeConstraint t1 t2 $ Just "ctx"



{-

----------------------------------------
-- Unification

_unify (Types.var "a") (Types.var "b")
_unify (Types.var "a") (Types.list $ Types.var "b")

_unify (Types.var "a") Types.int32

_unify (Types.list Types.string) (Types.list $ Types.var "a")

_unify (Types.map (Types.var "a") Types.int32) (Types.map Types.string (Types.var "b"))

sUnifyAll [Types.var "t1" === Types.var "t0", Types.var "t1" === Types.int32]

-- Failure cases

_unify Types.string Types.int32

_unify (Types.var "a") (Types.list $ Types.var "a")

ctx = Just "ctx"
uUnify [(TypeConstraint (Types.var "t1") (Types.var "t0") ctx), (TypeConstraint (Types.var "t1") Types.int32 ctx)]


----------------------------------------
-- Inference

_infer $ _str "hello"

_infer _add

_infer $ _list [_add]

_infer $ _lambda "x" $ _int 42

_infer $ _list [_int 42]




_inferRaw (_list [_int 42])



:module
import Hydra.NewInference

-- System F cases
_inferRaw (lambda "x" $ var "x")                                                           -- (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.var "t0"))
_inferRaw (int32 32 `with` ["foo">: lambda "x" $ var "x"])                                 -- (Types.mono Types.int32)
_inferRaw ((var "f" @@ int32 0) `with` ["f">: lambda "x" $ var "x"])                       -- (Types.mono Types.int32)
_inferRaw (var "f" `with` ["f">: (lambda "x" $ var "x") @@ int32 0])                       -- (Types.mono Types.int32)
_inferRaw (lambda "x" $ list [var "x"])                                                    -- (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.list (Types.var "t0")))
_inferRaw (var "sng" `with` ["sng">: lambda "x" $ list [var "x"]])                         -- (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.list (Types.var "t0")))
_inferRaw ((var "+" @@ (primSucc @@ (primSucc @@ int32 0)) @@ (primSucc @@ int32 0)) `with` ["+">: lambda "x" $ lambda "y" (primSucc @@ (var "+" @@ (primPred @@ var "x") @@ var "y"))]) -- (Types.mono Types.int32)
_inferRaw (var "f" `with` ["f">: lambda "x" $ lambda "y" (var "f" @@ int32 0 @@ var "x")]) -- (Types.poly ["t0"] $ Types.function Types.int32 (Types.function Types.int32 (Types.var "t0")))



_inferRaw (var "f" `with` ["f">: lambda "x" $ lambda "y" (var "f" @@ int32 0 @@ var "x")]) -- (Types.poly ["t0"] $ Types.function Types.int32 (Types.function Types.int32 (Types.var "t0")))



:set +m

constraints = [
  _con (Types.function (Types.var "t5") (Types.var "t6")) (Types.var "t0"),
  _con (Types.var "t5") Types.int32,
  _con (Types.function (Types.var "t3") (Types.var "t4")) (Types.var "t6"),
  _con (Types.var "t3") (Types.var "t1"),
  _con (Types.var "t0") (Types.function (Types.var "t1") (Types.function (Types.var "t2") (Types.var "t4")))]

uUnify constraints




_inferRaw (_lambda "x" $ _list [_var "x", _int 42])

_inferRaw (_lambda "y" (_a (_lambda "x" $ _list [_var "x"]) (_var "y")))




_inferRaw (var "sng" `with` ["sng">: lambda "x" $ list [var "x"]])


----------------------------------------
-- Instantiation

sInstantiate (Types.poly ["t0", "t1"] $ Types.function (Types.var "t1") (Types.var "t1")) sInitialContext



-}
