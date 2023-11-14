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


type Subst = M.Map Name Type

-- | The effect of applying the composition of s1 and s2 is the same as that of applying s2, then applying s1
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = M.union s1 $ M.map (substituteTypeVariables s1) s2

isTemporaryVariable :: Name -> Bool
isTemporaryVariable (Name s) = L.take 3 s == "tv_"

normalVariables :: [Name]
normalVariables = normalVariable <$> [0..]

-- | Type variable naming convention follows Haskell: t0, t1, etc.
normalVariable :: Int -> Name
normalVariable i = Name $ "t" ++ show i

substituteTypeVariable :: Name -> Type -> Type -> Type
substituteTypeVariable v subst = substituteTypeVariables (M.singleton v subst)

-- Note: this function does not expect to be given universal (lambda) types
substituteTypeVariables :: M.Map Name Type -> Type -> Type
substituteTypeVariables bindings = rewriteType f
  where
    f recurse original = case original of
      TypeVariable v -> M.findWithDefault original v bindings
      _ -> recurse original

temporaryVariables :: [Name]
temporaryVariables = temporaryVariable <$> [0..]

temporaryVariable :: Int -> Name
temporaryVariable i = Name $ "tv_" ++ show i
