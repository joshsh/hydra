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

-- TODO: restore normalization

--normalizeScheme :: Show a => TypeScheme a -> TypeScheme a
--normalizeScheme ts@(TypeScheme _ body) = TypeScheme (fmap snd ord) (normalizeType body)
--  where
--    ord = L.zip (S.toList $ freeVariablesInType body) normalVariables
--
--    normalizeFieldType (FieldType fname typ) = FieldType fname $ normalizeType typ
--
--    normalizeType typ = case typ of
--      TypeApplication (ApplicationType lhs rhs) -> TypeApplication (ApplicationType (normalizeType lhs) (normalizeType rhs))
--      TypeAnnotated (Annotated t ann) -> TypeAnnotated (Annotated (normalizeType t) ann)
--      TypeFunction (FunctionType dom cod) -> function (normalizeType dom) (normalizeType cod)
--      TypeList t -> list $ normalizeType t
--      TypeLiteral _ -> typ
--      TypeMap (MapType kt vt) -> Types.map (normalizeType kt) (normalizeType vt)
--      TypeOptional t -> optional $ normalizeType t
--      TypeProduct types -> TypeProduct (normalizeType <$> types)
--      TypeRecord (RowType n e fields) -> TypeRecord $ RowType n e (normalizeFieldType <$> fields)
--      TypeSet t -> set $ normalizeType t
--      TypeSum types -> TypeSum (normalizeType <$> types)
--      TypeUnion (RowType n e fields) -> TypeUnion $ RowType n e (normalizeFieldType <$> fields)
--      TypeLambda (LambdaType v t) -> TypeLambda (LambdaType v $ normalizeType t)
--      TypeVariable v -> case Prelude.lookup v ord of
--        Just (Name v1) -> var v1
--        Nothing -> error $ "type variable " ++ show v ++ " not in signature of type scheme: " ++ show ts
--      TypeWrap _ -> typ

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
