-- | Variable substitution and normalization of type expressions
module Hydra.Substitution where

import Hydra.Core
import Hydra.Mantle
import Hydra.Rewriting
import Hydra.Tier1
import Hydra.Dsl.Types as Types

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


type Subst a = M.Map Name (Type a)

composeSubst :: Subst a -> Subst a -> Subst a
composeSubst s1 s2 = M.union s1 $ M.map (substituteTypeVariables s1) s2

normalVariables :: [Name]
normalVariables = normalVariable <$> [0..]

-- | Type variable naming convention follows Haskell: t0, t1, etc.
normalVariable :: Int -> Name
normalVariable i = Name $ "t" ++ show i

normalizeTypeVariables :: Type a -> Type a
normalizeTypeVariables = rewriteType (findLambdas 0 M.empty) id
  where
    findLambdas idx subst recurse typ = case typ of
      TypeLambda (LambdaType v body) -> TypeLambda $ LambdaType v2 $ rewriteType (findLambdas idx2 subst2) id body
        where
          v2 = normalVariable idx
          idx2 = idx + 1
          subst2 = M.insert v v2 subst
      TypeVariable v -> TypeVariable $ case M.lookup v subst of
        Just v2 -> v2
        Nothing -> v
      _ -> recurse typ

substituteTypeVariable :: Name -> Type a -> Type a -> Type a
substituteTypeVariable v subst = substituteTypeVariables (M.singleton v subst)

substituteTypeVariables :: M.Map Name (Type a) -> Type a -> Type a
substituteTypeVariables bindings = rewriteType f id
  where
    f recurse original = case original of
      TypeLambda (LambdaType v body) -> case M.lookup v bindings of
        Nothing -> recurse original
        Just subst -> case subst of
          TypeVariable v2 -> TypeLambda (LambdaType v2 (recurse body))
          _ -> recurse body
      TypeVariable v -> M.findWithDefault original v bindings
      _ -> recurse original
