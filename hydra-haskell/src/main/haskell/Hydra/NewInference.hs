module Hydra.NewInference where

import Hydra.Basics
import Hydra.Core
import Hydra.Compute
import Hydra.Mantle
import qualified Hydra.Tier1 as Tier1
import qualified Hydra.Lib.Flows as Flows

import qualified Data.List as L
import qualified Data.Map as M


--------------------------------------------------------------------------------
-- Graphs

type SLexicon = M.Map Name TypeScheme

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

data SApplicationTerm = SApplicationTerm STerm STerm deriving (Eq, Ord, Show)
data SLambda = SLambda Name STerm deriving (Eq, Ord, Show)
-- TODO: modify to use multiple bindings
data SLet = SLet SField STerm deriving (Eq, Ord, Show)
data SField = SField Name STerm deriving (Eq, Ord, Show)

data STerm
  = STermApplication SApplicationTerm
  | STermLambda SLambda
  | STermMap (M.Map STerm STerm)
  | STermLet SLet
  | STermList [STerm]
  | STermLiteral Literal
  | STermPrimitive Name
  | STermTuple [STerm]
--  | STermTyped STerm TypeScheme
  | STermVariable Name
  deriving (Eq, Ord, Show)


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
-- Flows

fromEither :: Show e => Either e a -> Flow c a
fromEither x = case x of
  Left e -> Flows.fail $ show e
  Right a -> Flows.pure a

pam :: Flow s a -> (a -> b) -> Flow s b
pam m f = fmap f m

--------------------------------------------------------------------------------
-- Inference

data SInferenceContext
  = SInferenceContext {
    sInferenceContextLexicon :: SLexicon,
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

data TypeInferenceError
  = TypeInferenceErrorNoSuchPrimitive Name
  | TypeInferenceErrorNotYetSupported
  | TypeInferenceErrorVariableNotBoundToType Name
  deriving (Eq, Ord, Show)

sInferType :: STerm -> Flow SInferenceContext TypeScheme
sInferType term = Flows.bind (sInferTypeInternal term) unifyAndSubst
  where
    unifyAndSubst :: SInferenceResult -> Flow SInferenceContext TypeScheme
    unifyAndSubst result = Flows.bind (fromEither $ uUnify $ sInferenceResultConstraints result) doSubst
      where
        doSubst :: SSubst -> Flow SInferenceContext TypeScheme
        doSubst subst = sInstantiateAndNormalize $ sSubstituteTypeVariablesInScheme subst $ sInferenceResultScheme result

sInferTypeInternal :: STerm -> Flow SInferenceContext SInferenceResult
sInferTypeInternal term = case term of

    STermApplication (SApplicationTerm lterm rterm) -> Flows.bind sNewVar withVar1
      where
        withVar1 dom = Flows.bind sNewVar withVar2
          where
            withVar2 cod = Flows.bind (sInferTypeInternal lterm) withLeft
              where
                withLeft lresult = Flows.bind (sInferTypeInternal rterm) withRight
                  where
                    withRight rresult = Flows.pure $ SInferenceResult (TypeScheme tvars $ TypeVariable cod) $ [
                        TypeConstraint (tyfun (TypeVariable dom) (TypeVariable cod)) ltyp ctx,
                        TypeConstraint (TypeVariable dom) rtyp ctx]
                        ++ sInferenceResultConstraints lresult ++ sInferenceResultConstraints rresult
                      where
                        ctx = Just "application"
                        ltyp = typeSchemeType $ sInferenceResultScheme lresult
                        rtyp = typeSchemeType $ sInferenceResultScheme rresult
                        tvars = typeSchemeVariables (sInferenceResultScheme lresult) ++ typeSchemeVariables (sInferenceResultScheme rresult)

    STermLambda (SLambda var body) -> Flows.bind sNewVar withVar
     where
        withVar tvar = sWithTypeBinding var (tymono $ TypeVariable tvar) $ Flows.map withBodyType (sInferTypeInternal body)
          where
            -- TODO: prove that tvar will never appear in vars
            withBodyType (SInferenceResult (TypeScheme vars t) constraints)
              = SInferenceResult (TypeScheme (tvar:vars) $ tyfun (TypeVariable tvar) t) constraints

    -- TODO: propagate rawValueVars and envVars into the final result, possibly after substitution
    -- TODO: recursive and mutually recursive let
    STermLet (SLet (SField key value) env) -> Flows.bind sNewVar withVar
      where
        -- Create a temporary type variable for the binding
        withVar var = sWithTypeBinding key (tymono $ TypeVariable var) $
            Flows.bind (sInferTypeInternal value) withValueType
          where
            -- Unify and substitute over the value constraints
            -- TODO: save the substitution and pass it along, instead of the original set of constraints
            withValueType (SInferenceResult rawValueScheme valueConstraints) = Flows.bind (fromEither $ uUnify kvConstraints) afterUnification
              where
                rawValueVars = typeSchemeVariables rawValueScheme
                kvConstraints = bindingConstraint:valueConstraints
                bindingConstraint = TypeConstraint (TypeVariable var) (typeSchemeType rawValueScheme) $ Just "let binding"
                -- Now update the type binding to use the inferred type
                afterUnification subst = sWithTypeBinding key valueScheme
                    $ Flows.map withEnvType (sInferTypeInternal env)
                  where
                    valueScheme = sSubstituteTypeVariablesInScheme subst rawValueScheme
                    withEnvType (SInferenceResult envScheme envConstraints) = SInferenceResult envScheme constraints
                      where
                        constraints = kvConstraints ++ envConstraints
                        envVars = typeSchemeVariables envScheme

    STermList els -> Flows.bind sNewVar withVar
      where
        withVar tvar = if L.null els
            then Flows.pure $ yield (TypeScheme [tvar] $ tylist $ TypeVariable tvar) []
            else pam (Flows.sequence (sInferTypeInternal <$> els)) fromResults
          where
            fromResults results = yield (TypeScheme vars $ tylist $ TypeVariable tvar) constraints
              where
                uctx = Just "list element"
                constraints = cinner ++ couter
                cinner = L.concat (sInferenceResultConstraints <$> results)
                couter = fmap (\t -> TypeConstraint (TypeVariable tvar) t uctx) types
                types = typeSchemeType . sInferenceResultScheme <$> results
                vars = L.concat (typeSchemeVariables . sInferenceResultScheme <$> results)

    STermLiteral lit -> Flows.pure $ yieldWithoutConstraints $ tymono $ TypeLiteral $ literalType lit

    STermMap m -> Flows.bind sNewVar withKeyVar
      where
        withKeyVar kvar = Flows.bind sNewVar withValueVar
          where
            withValueVar vvar = if M.null m
               then Flows.pure $ yield (TypeScheme [kvar, vvar] $ tymap (TypeVariable kvar) (TypeVariable vvar)) []
               else pam (Flows.sequence $ fmap fromPair $ M.toList m) withResults
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
                withResults pairs = yield (TypeScheme (L.concat (fst <$> pairs)) $ tymap (TypeVariable kvar) (TypeVariable vvar)) $
                  L.concat (snd <$> pairs)

    STermPrimitive name -> Flow $ \ctx t -> case M.lookup name (sInferenceContextLexicon ctx) of
      Just scheme -> unFlow (Flows.map withoutConstraints $ sInstantiate scheme) ctx t
      Nothing -> unFlow (Flows.fail $ show $ TypeInferenceErrorNoSuchPrimitive name) ctx t

    STermTuple els -> if L.null els
      then Flows.pure $ yield (tymono $ typrod []) []
      else pam (Flows.sequence (sInferTypeInternal <$> els)) fromResults
      where
        fromResults results = yield (TypeScheme tvars $ TypeProduct tbodies) constraints
          where
            tvars = L.concat $ typeSchemeVariables . sInferenceResultScheme <$> results
            tbodies = typeSchemeType . sInferenceResultScheme <$> results
            constraints = L.concat $ sInferenceResultConstraints <$> results

    STermVariable var -> Flow $ \ctx t -> case M.lookup var (sInferenceContextTypingEnvironment ctx) of
      Just scheme -> unFlow (Flows.map withoutConstraints $ sInstantiate scheme) ctx t
      Nothing -> unFlow (Flows.fail $ show $ TypeInferenceErrorVariableNotBoundToType var) ctx t

  where
    unsupported = Flows.fail $ show TypeInferenceErrorNotYetSupported
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

tyfun d c = TypeFunction $ FunctionType d c
tyint = TypeLiteral $ LiteralTypeInteger $ IntegerTypeInt32
tylist = TypeList
tymap k v = TypeMap $ MapType k v
typair l r = TypeProduct [l, r]
typrod = TypeProduct
tymono = TypeScheme []
typoly vars = TypeScheme (Name <$> vars)
tystr = TypeLiteral LiteralTypeString
tyvar = TypeVariable . Name

_app l r = STermApplication $ SApplicationTerm l r
_int = STermLiteral . LiteralInteger . IntegerValueInt32
_lambda v b = STermLambda $ SLambda (Name v) b
_list = STermList
_map = STermMap
_pair l r = STermTuple [l, r]
_str = STermLiteral . LiteralString
_var = STermVariable . Name





(@@) :: STerm -> STerm -> STerm
f @@ x = STermApplication $ SApplicationTerm f x

infixr 0 >:
(>:) :: String -> STerm -> (Name, STerm)
n >: t = (Name n, t)

int32 = STermLiteral . LiteralInteger . IntegerValueInt32
lambda v b = STermLambda $ SLambda (Name v) b
list = STermList
map = STermMap
pair l r = STermTuple [l, r]
string = STermLiteral . LiteralString
var = STermVariable . Name
with env bindings = L.foldl (\e (k, v) -> STermLet $ SLet (SField k v) e) env bindings




infixr 0 ===
(===) :: Type -> Type -> TypeConstraint
t1 === t2 = TypeConstraint t1 t2 $ Just "some context"


_add = STermPrimitive $ Name "add"
primPred = STermPrimitive $ Name "primPred"
primSucc = STermPrimitive $ Name "primSucc"

_unify t1 t2 = uUnify [TypeConstraint t1 t2 $ Just "ctx"]

sTestLexicon = M.fromList [
  (Name "add", tymono $ tyfun tyint tyint),
  (Name "primPred", tymono $ tyfun tyint tyint),
  (Name "primSucc", tymono $ tyfun tyint tyint)]

sInitialContext = SInferenceContext sTestLexicon 0 M.empty

_infer term = flowStateValue $ unFlow (sInferType term) sInitialContext Tier1.emptyTrace

_inferRaw term = flowStateValue $ unFlow (sInferTypeInternal term) sInitialContext Tier1.emptyTrace

_instantiate scheme = flowStateValue $ unFlow (sInstantiate scheme) sInitialContext Tier1.emptyTrace

_con t1 t2 = TypeConstraint t1 t2 $ Just "ctx"



{-

----------------------------------------
-- Unification

_unify (tyvar "a") (tyvar "b")
_unify (tyvar "a") (tylist $ tyvar "b")

_unify (tyvar "a") tyint

_unify (tylist tystr) (tylist $ tyvar "a")

_unify (tymap (tyvar "a") tyint) (tymap tystr (tyvar "b"))

sUnifyAll [tyvar "t1" === tyvar "t0", tyvar "t1" === tyint]

-- Failure cases

_unify tystr tyint

_unify (tyvar "a") (tylist $ tyvar "a")

ctx = Just "ctx"
uUnify [(TypeConstraint (tyvar "t1") (tyvar "t0") ctx), (TypeConstraint (tyvar "t1") tyint ctx)]


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
_inferRaw (lambda "x" $ var "x")                                                           -- (typoly ["t0"] $ tyfun (tyvar "t0") (tyvar "t0"))
_inferRaw (int32 32 `with` ["foo">: lambda "x" $ var "x"])                                 -- (tymono tyint)
_inferRaw ((var "f" @@ int32 0) `with` ["f">: lambda "x" $ var "x"])                       -- (tymono tyint)
_inferRaw (var "f" `with` ["f">: (lambda "x" $ var "x") @@ int32 0])                       -- (tymono tyint)
_inferRaw (lambda "x" $ list [var "x"])                                                    -- (typoly ["t0"] $ tyfun (tyvar "t0") (tylist (tyvar "t0")))
_inferRaw (var "sng" `with` ["sng">: lambda "x" $ list [var "x"]])                         -- (typoly ["t0"] $ tyfun (tyvar "t0") (tylist (tyvar "t0")))
_inferRaw ((var "+" @@ (primSucc @@ (primSucc @@ int32 0)) @@ (primSucc @@ int32 0)) `with` ["+">: lambda "x" $ lambda "y" (primSucc @@ (var "+" @@ (primPred @@ var "x") @@ var "y"))]) -- (tymono tyint)
_inferRaw (var "f" `with` ["f">: lambda "x" $ lambda "y" (var "f" @@ int32 0 @@ var "x")]) -- (typoly ["t0"] $ tyfun tyint (tyfun tyint (tyvar "t0")))



_inferRaw (var "f" `with` ["f">: lambda "x" $ lambda "y" (var "f" @@ int32 0 @@ var "x")]) -- (typoly ["t0"] $ tyfun tyint (tyfun tyint (tyvar "t0")))



:set +m

constraints = [
  _con (tyfun (tyvar "t5") (tyvar "t6")) (tyvar "t0"),
  _con (tyvar "t5") tyint,
  _con (tyfun (tyvar "t3") (tyvar "t4")) (tyvar "t6"),
  _con (tyvar "t3") (tyvar "t1"),
  _con (tyvar "t0") (tyfun (tyvar "t1") (tyfun (tyvar "t2") (tyvar "t4")))]

uUnify constraints




_inferRaw (_lambda "x" $ _list [_var "x", _int 42])

_inferRaw (_lambda "y" (_a (_lambda "x" $ _list [_var "x"]) (_var "y")))




_inferRaw (var "sng" `with` ["sng">: lambda "x" $ list [var "x"]])


----------------------------------------
-- Instantiation

sInstantiate (typoly ["t0", "t1"] $ tyfun (tyvar "t1") (tyvar "t1")) sInitialContext



-}
