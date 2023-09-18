-- | Hindley-Milner style type unification

module Hydra.Unification (
  Constraint,
  solveConstraints,
) where

import Hydra.Basics
import Hydra.Strip
import Hydra.Compute
import Hydra.Core
import Hydra.Lexical
import Hydra.Printing
import Hydra.Rewriting
import Hydra.Substitution
import Hydra.Tier1
import Hydra.Dsl.Types as Types

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S


type Constraint = (Type, Type)

type Unifier = (Subst, [Constraint])

-- Note: type variables in Hydra are allowed to bind to type expressions which contain the variable;
--       i.e. type recursion by name is allowed.
bind :: Name -> Type -> Flow s (Subst)
bind name typ = do
  if typ == TypeVariable name
  then return M.empty
  else if variableOccursInType name typ
--     then fail $ "infinite type for " ++ unName name ++ ": " ++ show typ
    then return M.empty
    else return $ M.singleton name typ

solveConstraints :: [Constraint] -> Flow s (Subst)
solveConstraints constraints = solveConstraintsInternal (M.empty, constraints)

solveConstraintsInternal :: Unifier -> Flow s (Subst)
solveConstraintsInternal (su, cs) = case cs of
  [] -> return su
  ((t1, t2):rest) -> do
    su1  <- unify t1 t2
    solveConstraintsInternal (
      composeSubst su1 su,
      (\(t1, t2) -> (substituteTypeVariables su1 t1, substituteTypeVariables su1 t2)) <$> rest)

unify :: Type -> Type -> Flow s (Subst)
unify ltyp rtyp = do
--     withTrace ("unify " ++ show ltyp ++ " with " ++ show rtyp) $
     case (stripType ltyp, stripType rtyp) of

       -- Symmetric patterns
      (TypeApplication (ApplicationType lhs1 rhs1), TypeApplication (ApplicationType lhs2 rhs2)) ->
        unifyMany [lhs1, rhs1] [lhs2, rhs2]
      (TypeFunction (FunctionType dom1 cod1), TypeFunction (FunctionType dom2 cod2)) ->
        unifyMany [dom1, cod1] [dom2, cod2]
      (TypeList lt1, TypeList lt2) -> unify lt1 lt2
      (TypeLiteral lt1, TypeLiteral lt2) -> verify $ lt1 == lt2
      (TypeMap (MapType k1 v1), TypeMap (MapType k2 v2)) -> unifyMany [k1, v1] [k2, v2]
      (TypeOptional ot1, TypeOptional ot2) -> unify ot1 ot2
      (TypeProduct types1, TypeProduct types2) -> unifyMany types1 types2
      (TypeRecord rt1, TypeRecord rt2) -> do
        verify (rowTypeTypeName rt1 == rowTypeTypeName rt2)
        verify (L.length (rowTypeFields rt1) == L.length (rowTypeFields rt2))
        unifyMany (fieldTypeType <$> rowTypeFields rt1) (fieldTypeType <$> rowTypeFields rt2)
      (TypeSet st1, TypeSet st2) -> unify st1 st2
      (TypeUnion rt1, TypeUnion rt2) -> verify (rowTypeTypeName rt1 == rowTypeTypeName rt2)
      (TypeSum types1, TypeSum types2) -> unifyMany types1 types2
      (TypeWrap n1, TypeWrap n2) -> verify $ n1 == n2

      -- Asymmetric patterns
      (TypeVariable v1, TypeVariable v2) -> bindWeakest v1 v2
      (TypeVariable v, t2) -> bind v t2
      (t1, TypeVariable v) -> bind v t1
      (TypeLambda lt, t2) -> unifyLambda lt t2
      (t1, TypeLambda lt) -> unifyLambda lt t1
      (TypeApplication (ApplicationType lhs rhs), t2) -> unify lhs t2
      (t1, TypeApplication (ApplicationType lhs rhs)) -> unify t1 lhs

      (l, r) -> fail $ "unification of " ++ show (typeVariant l) ++ " with " ++ show (typeVariant r) ++
        ":\n  " ++ show l ++
        "\n  " ++ show r
  where
    verify b = if b then return M.empty else failUnification
    failUnification = fail $ "could not unify type " ++ show (stripType ltyp) ++ " with " ++ show (stripType rtyp)
--     failUnification = fail $ "could not unify type " ++ describeType (stripType ltyp) ++ " with " ++ describeType (stripType rtyp)
    bindWeakest v1 v2 = if isWeak v1
        then bind v1 (TypeVariable v2)
        else bind v2 (TypeVariable v1)
      where
        isWeak v = L.head (unName v) == 't' -- TODO: use a convention like _xxx for temporarily variables, then normalize and replace them
    unifyLambda (LambdaType v body) other = case other of
      TypeLambda (LambdaType v2 body2) -> unifyMany [TypeVariable v, body] [TypeVariable v2, body2]
      _ -> unify body other
--      _ -> fail $ "could not unify with lambda type: " ++ show (stripType ltyp)

unifyMany :: [Type] -> [Type] -> Flow s (Subst)
unifyMany [] [] = return M.empty
unifyMany (t1 : ts1) (t2 : ts2) =
  do su1 <- unify t1 t2
     su2 <- unifyMany (substituteTypeVariables su1 <$> ts1) (substituteTypeVariables su1 <$> ts2)
     return (composeSubst su2 su1)
unifyMany t1 t2 = fail $ "unification mismatch between " ++ show t1 ++ " and " ++ show t2

variableOccursInType :: Name -> Type -> Bool
variableOccursInType a t = S.member a $ freeVariablesInType t
