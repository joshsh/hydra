-- | Variable substitution and normalization of type expressions
module Hydra.Substitution where

import Hydra.Core
import Hydra.Compute
import Hydra.Graph
import Hydra.Annotations
import Hydra.Mantle
import Hydra.Rewriting
import Hydra.Tier1
import Hydra.Tier2
import Hydra.Dsl.Types as Types

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


type Subst = M.Map Name Type

-- | The effect of applying the composition of s1 and s2 is the same as that of applying s2, then applying s1
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = M.union s1 $ M.map (substituteTypeVariables s1) s2

freshName :: Flow Graph Name
freshName = temporaryVariable <$> nextCount "hyInf"

freshTypeVariable :: Flow Graph Type
freshTypeVariable = TypeVariable <$> freshName

-- | Create a copy of a type in which all bound type variables are replaced with fresh variables.
--   Replacing variables prevents type variables from being reused across multiple instantiations of a primitive
--   or occurrences of a named type, or from conflation of type variables across primitives or elements,
--   either of which could lead to false unification.
instantiate :: Type -> Flow Graph Type
instantiate t = do
    g <- getState
    subst <- M.fromList <$> (CM.mapM toPair $ L.nub $ boundVariablesInTypeOrdered t)
    return $ replaceTypeVariables subst t
  where
    toPair v = do
      v' <- freshName
      return (v, v')

isTemporaryVariable :: Name -> Bool
isTemporaryVariable (Name s) = L.take 3 s == "tv_"

normalVariables :: [Name]
normalVariables = normalVariable <$> [0..]

-- | Type variable naming convention follows Haskell: t0, t1, etc.
normalVariable :: Int -> Name
normalVariable i = Name $ "t" ++ show i

-- | Replace arbitrary bound type variables like v, a, v_12 with the systematic type variables t0, t1, t2, ...
--   following a canonical ordering in the term.
--   This function assumes that the bound variables do not also appear free in the type expressions of the term,
--   which in Hydra is made less likely by using the unusual naming convention tv_0, tv_1, etc. for temporary variables.
normalizeBoundTypeVariablesInSystemFTerm :: Term -> Term
normalizeBoundTypeVariablesInSystemFTerm term = replaceTypeVariablesInSystemFTerm subst term
  where
    actualVars = boundTypeVariablesInSystemFTerm term
    subst = M.fromList $ L.zip actualVars normalVariables

replaceTypeVariables :: M.Map Name Name -> Type -> Type
replaceTypeVariables subst = rewriteType $ \recurse t -> case recurse t of
    TypeVariable v -> TypeVariable $ replace v
    TypeLambda (LambdaType v body) -> TypeLambda $ LambdaType (replace v) body
    t1 -> t1
  where
    replace v = M.findWithDefault v v subst

substituteTypeVariable :: Name -> Type -> Type -> Type
substituteTypeVariable v subst = substituteTypeVariables (M.singleton v subst)

-- Note: this function does not expect to be given universal (lambda) types
substituteTypeVariables :: M.Map Name Type -> Type -> Type
substituteTypeVariables bindings = rewriteType f
  where
    f recurse original = case original of
      TypeVariable v -> M.findWithDefault original v bindings
      _ -> recurse original

-- Note: this will replace all occurrences, regardless of boundness or shadowing
replaceTypeVariablesInSystemFTerm :: M.Map Name Name -> Term -> Term
replaceTypeVariablesInSystemFTerm subst = rewriteTerm $ \recurse term ->
  case recurse term of
    TermFunction (FunctionLambda (Lambda v (Just mt) body)) -> TermFunction $ FunctionLambda $ Lambda v (Just mt2) body
      where
        mt2 = replaceTypeVariables subst mt
    TermTypeAbstraction (TypeAbstraction v body) -> TermTypeAbstraction $ TypeAbstraction v2 body
      where
        v2 = M.findWithDefault v v subst
    TermTyped (TypedTerm typ term) -> TermTyped $ TypedTerm (replaceTypeVariables subst typ) term
    t -> t

temporaryVariables :: [Name]
temporaryVariables = temporaryVariable <$> [0..]

temporaryVariable :: Int -> Name
temporaryVariable i = Name $ "tv_" ++ show i
