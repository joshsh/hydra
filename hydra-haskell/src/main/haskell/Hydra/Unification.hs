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


-- | A constraint is a pair of types which are to be unified as a single type
type Constraint = (Type, Type)

-- Note: type variables in Hydra are allowed to bind to type expressions which contain the variable;
--       i.e. type recursion by name is allowed.
bind :: Name -> Type -> Flow s Subst
bind name typ = do
  if typ == TypeVariable name
  then return M.empty
  else if S.member name $ freeVariablesInType typ
--     then fail $ "infinite type for " ++ unName name ++ ": " ++ show typ
    then return M.empty
    else return $ M.singleton name typ

-- Enforces a convention which favors user-provided type variables over temporary variables
bindWeakest :: Name -> Name -> Flow s Subst
bindWeakest v1 v2 = if isTemporaryVariable v1
    then bind v1 (TypeVariable v2)
    else bind v2 (TypeVariable v1)

failUnification :: Flow s Subst
failUnification = fail "could not unify types"

failUnificationOf :: Type -> Type -> Flow s Subst
failUnificationOf l r = fail $ "could not unify " ++ show (typeVariant l) ++ " with " ++ show (typeVariant r) ++
  ":\n  " ++ show l ++ "\n  " ++ show r

-- | Currently, we ignore both annotations and universal types for the purpose of unification.
--   Annotations are simply discarded, whereas universal types are initially discarded,
--   then reconstructed in a normal form after unification.
normalizeForUnification :: Type -> Type
normalizeForUnification = rewriteType $ \recurse t -> case recurse t of
  TypeAnnotated (Annotated subj _) -> subj
  TypeLambda (LambdaType _ body) -> body
  t1 -> t1

-- | Create a substitution (of type variables for types) based on a set of constraints
solveConstraints :: [Constraint] -> Flow s Subst
solveConstraints constraints = solve M.empty constraints

solve :: Subst -> [Constraint] -> Flow s Subst
solve su cs = case cs of
  [] -> return su
  ((t1, t2):rest) -> do
    su1  <- unify (normalizeForUnification t1) (normalizeForUnification t2)
    solve
      (composeSubst su1 su)
      ((\(t1, t2) -> (substituteTypeVariables su1 t1, substituteTypeVariables su1 t2)) <$> rest)

unify :: Type -> Type -> Flow s Subst
unify ltyp rtyp = withTrace ("unify " ++ show ltyp ++ " with " ++ show rtyp) $ do
  case (ltyp, rtyp) of
    -- Variables are special; a variable either on the right or the left can be bound to the expression on the other side
    (TypeVariable v, t2) -> unifyTypeVariable v t2
    (t1, TypeVariable v) -> unifyTypeVariable v t1

    -- All other unification patterns are symmetrical; they require the same type variant on the left and the right
    (TypeApplication (ApplicationType lhs1 rhs1), TypeApplication (ApplicationType lhs2 rhs2))
      -> unifyMany [lhs1, rhs1] [lhs2, rhs2]
    (TypeFunction (FunctionType dom1 cod1), TypeFunction (FunctionType dom2 cod2))
      -> unifyMany [dom1, cod1] [dom2, cod2]
    (TypeList lt1, TypeList lt2) -> unify lt1 lt2
    (TypeLiteral lt1, TypeLiteral lt2) -> verify $ lt1 == lt2
    (TypeMap (MapType k1 v1), TypeMap (MapType k2 v2)) -> unifyMany [k1, v1] [k2, v2]
    (TypeOptional ot1, TypeOptional ot2) -> unify ot1 ot2
    (TypeProduct types1, TypeProduct types2) -> unifyMany types1 types2
    (TypeRecord rt1, TypeRecord rt2) -> unifyRowType rt1 rt2
    (TypeSet st1, TypeSet st2) -> unify st1 st2
    (TypeUnion rt1, TypeUnion rt2) -> unifyRowType rt1 rt2
    (TypeSum types1, TypeSum types2) -> unifyMany types1 types2
    (TypeWrap nt1, TypeWrap nt2) -> unifyNominalType nt1 nt2

    _ -> failUnificationOf ltyp rtyp

unifyMany :: [Type] -> [Type] -> Flow s Subst
unifyMany [] [] = return M.empty
unifyMany (t1 : rest1) (t2 : rest2) =
  do su1 <- unify t1 t2
     su2 <- unifyMany (substituteTypeVariables su1 <$> rest1) (substituteTypeVariables su1 <$> rest2)
     return (composeSubst su2 su1)
unifyMany t1 t2 = fail $ "unification mismatch between " ++ show t1 ++ " and " ++ show t2

unifyNominalType :: Nominal Type -> Nominal Type -> Flow s Subst
unifyNominalType nt1 nt2 = do
  verify $ nominalTypeName nt1 == nominalTypeName nt2
  unify (nominalObject nt1) (nominalObject nt2)

unifyRowType :: RowType -> RowType -> Flow s Subst
unifyRowType rt1 rt2 = do
  verify (rowTypeTypeName rt1 == rowTypeTypeName rt2)
  verify (L.length (rowTypeFields rt1) == L.length (rowTypeFields rt2))
  unifyMany (fieldTypeType <$> rowTypeFields rt1) (fieldTypeType <$> rowTypeFields rt2)

unifyTypeVariable :: Name -> Type -> Flow s Subst
unifyTypeVariable name other = case other of
  TypeVariable name2 -> bindWeakest name name2
  _ -> bind name other

verify :: Bool -> Flow s Subst
verify b = if b then return M.empty else failUnification
