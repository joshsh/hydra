module Hydra.Ext.Python.Utils where

import qualified Hydra.Ext.Python.Syntax as Py

import qualified Data.List as L


assignmentStatement :: Py.Name -> Py.Expression -> Py.Statement
assignmentStatement name expr = pyAssignmentToPyStatement $ Py.AssignmentUntyped $ Py.UntypedAssignment
    [pyNameToPyStarTarget name]
    (pyExpressionToPyAnnotatedRhs expr)
    Nothing

annotatedExpression :: Maybe String -> Py.Expression -> Py.Expression
annotatedExpression mcomment expr = case mcomment of
  Nothing -> expr
  Just c -> pyPrimaryToPyExpression $
    primaryWithExpressionSlices (pyNameToPyPrimary $ Py.Name "Annotated") [expr, stringToPyExpression c]

decodePyExpressionToPyPrimary :: Py.Expression -> Maybe Py.Primary
decodePyExpressionToPyPrimary e = case e of
  Py.ExpressionSimple (Py.Disjunction [conjunction]) -> decodePyConjunctionToPyPrimary conjunction
  _ -> Nothing

decodePyConjunctionToPyPrimary :: Py.Conjunction -> Maybe Py.Primary
decodePyConjunctionToPyPrimary c = case c of
  Py.Conjunction [inversion] -> decodePyInversionToPyPrimary inversion
  _ -> Nothing

decodePyInversionToPyPrimary :: Py.Inversion -> Maybe Py.Primary
decodePyInversionToPyPrimary i = case i of
  Py.InversionSimple comparison -> decodePyComparisonToPyAwaitPrimary comparison
  _ -> Nothing

decodePyComparisonToPyAwaitPrimary :: Py.Comparison -> Maybe Py.Primary
decodePyComparisonToPyAwaitPrimary c = case c of
  Py.Comparison (Py.BitwiseOr _ (Py.BitwiseXor _ (Py.BitwiseAnd _ (Py.ShiftExpression _ (Py.Sum _ (Py.Term _
    (Py.FactorSimple power))))))) _ -> decodePyPowerToPyPrimary power
  _ -> Nothing

decodePyPowerToPyPrimary :: Py.Power -> Maybe Py.Primary
decodePyPowerToPyPrimary p = case p of
  Py.Power (Py.AwaitPrimary False prim) _ -> Just prim
  _ -> Nothing

functionCall :: Py.Primary -> [Py.Expression] -> Py.Expression
functionCall func args = pyPrimaryToPyExpression $ primaryWithRhs func $
  Py.PrimaryRhsCall $ Py.Args (Py.PosArgExpression <$> args) [] []

nameAndParams :: Py.Name -> [Py.Expression] -> Py.Expression
nameAndParams pyName params = primaryAndParams (pyNameToPyPrimary pyName) params

newtypeStatement :: Py.Name -> Maybe String -> Py.Expression -> Py.Statement
newtypeStatement name mcomment expr = assignmentStatement name $ annotatedExpression mcomment $
  functionCall (pyNameToPyPrimary $ Py.Name "NewType") [stringToPyExpression $ Py.unName name, expr]

primaryAndParams :: Py.Primary -> [Py.Expression] -> Py.Expression
primaryAndParams prim params = pyPrimaryToPyExpression $ primaryWithExpressionSlices prim params

pyAssignmentToPyStatement :: Py.Assignment -> Py.Statement
pyAssignmentToPyStatement = pySimpleStatementToPyStatement . Py.SimpleStatementAssignment

pyAtomToPyExpression :: Py.Atom -> Py.Expression
pyAtomToPyExpression = pyPrimaryToPyExpression . Py.PrimarySimple

pyBitwiseOrToPyConjunction :: Py.BitwiseOr -> Py.Conjunction
pyBitwiseOrToPyConjunction bor = Py.Conjunction [Py.InversionSimple $ Py.Comparison bor []]

pyBitwiseOrToPyExpression :: Py.BitwiseOr -> Py.Expression
pyBitwiseOrToPyExpression = pyConjunctionToPyExpression . pyBitwiseOrToPyConjunction

pyConjunctionToPyExpression :: Py.Conjunction -> Py.Expression
pyConjunctionToPyExpression conj = Py.ExpressionSimple $ Py.Disjunction [conj]

-- Extracts the primary from an expression, or wraps it in parentheses if the expression does not contain a primary.
pyExpressionToPyPrimary :: Py.Expression -> Py.Primary
pyExpressionToPyPrimary e = case decodePyExpressionToPyPrimary e of
  Just prim -> prim
  Nothing -> Py.PrimarySimple $ Py.AtomGroup $ Py.GroupExpression $ Py.NamedExpressionSimple e

pyExpressionToPyAnnotatedRhs :: Py.Expression -> Py.AnnotatedRhs
pyExpressionToPyAnnotatedRhs expr = Py.AnnotatedRhsStar [Py.StarExpressionSimple expr]

pyExpressionToPySlice :: Py.Expression -> Py.Slice
pyExpressionToPySlice = Py.SliceNamed . Py.NamedExpressionSimple

pyNameToPyExpression :: Py.Name -> Py.Expression
pyNameToPyExpression =  pyPrimaryToPyExpression . pyNameToPyPrimary

pyNameToPyNamedExpression :: Py.Name -> Py.NamedExpression
pyNameToPyNamedExpression = Py.NamedExpressionSimple . pyNameToPyExpression

pyNameToPyPrimary :: Py.Name -> Py.Primary
pyNameToPyPrimary = Py.PrimarySimple . Py.AtomName

pyNameToPyStarTarget :: Py.Name -> Py.StarTarget
pyNameToPyStarTarget = Py.StarTargetUnstarred . Py.TargetWithStarAtomAtom . Py.StarAtomName

pyNameToPyTypeParameter :: Py.Name -> Py.TypeParameter
pyNameToPyTypeParameter name = Py.TypeParameterSimple $ Py.SimpleTypeParameter name Nothing Nothing

pyPrimaryToPyBitwiseOr :: Py.Primary -> Py.BitwiseOr
pyPrimaryToPyBitwiseOr = Py.BitwiseOr Nothing . pyPrimaryToPyBitwiseXor

pyPrimaryToPyBitwiseXor :: Py.Primary -> Py.BitwiseXor
pyPrimaryToPyBitwiseXor prim = Py.BitwiseXor Nothing $ Py.BitwiseAnd Nothing (Py.ShiftExpression Nothing $
  Py.Sum Nothing $ Py.Term Nothing $ Py.FactorSimple $ Py.Power (Py.AwaitPrimary False prim) Nothing)

pyPrimaryToPyConjunction :: Py.Primary -> Py.Conjunction
pyPrimaryToPyConjunction = pyBitwiseOrToPyConjunction . pyPrimaryToPyBitwiseOr

pyPrimaryToPyExpression :: Py.Primary -> Py.Expression
pyPrimaryToPyExpression = pyConjunctionToPyExpression . pyPrimaryToPyConjunction

pyPrimaryToPySlice :: Py.Primary -> Py.Slice
pyPrimaryToPySlice = pyExpressionToPySlice . pyPrimaryToPyExpression

pySimpleStatementToPyStatement :: Py.SimpleStatement -> Py.Statement
pySimpleStatementToPyStatement s = Py.StatementSimple [s]

orExpression :: [Py.Primary] -> Py.Expression
orExpression prims = pyBitwiseOrToPyExpression $ build Nothing prims
  where
    build prev prims = if L.null (L.tail prims)
        then cur
        else build (Just cur) $ L.tail prims
      where
        cur = Py.BitwiseOr prev $ pyPrimaryToPyBitwiseXor $ L.head prims

orNull :: Py.Primary -> Py.Expression
orNull lhs = orExpression [lhs, pyNameToPyPrimary $ Py.Name "None"]

primaryWithRhs :: Py.Primary -> Py.PrimaryRhs -> Py.Primary
primaryWithRhs prim rhs = Py.PrimaryCompound $ Py.PrimaryWithRhs prim rhs

primaryWithExpressionSlices :: Py.Primary -> [Py.Expression] -> Py.Primary
primaryWithExpressionSlices prim exprs = primaryWithSlices prim
  (pyExpressionToPySlice $ head exprs)
  (Py.SliceOrStarredExpressionSlice . pyExpressionToPySlice <$> tail exprs)

primaryWithSlices :: Py.Primary -> Py.Slice -> [Py.SliceOrStarredExpression] -> Py.Primary
primaryWithSlices prim first rest = primaryWithRhs prim $ Py.PrimaryRhsSlices $ Py.Slices first rest

stringToPyExpression :: String -> Py.Expression
stringToPyExpression = pyAtomToPyExpression . Py.AtomString

typeAliasStatement :: Py.Name -> Maybe String -> Py.Expression -> Py.Statement
--typeAliasStatement name mcomment tyexpr = pySimpleStatementToPyStatement $
--  Py.SimpleStatementTypeAlias $ Py.TypeAlias name [] $ annotatedExpression mcomment tyexpr
typeAliasStatement name mcomment tyexpr = assignmentStatement name $ annotatedExpression mcomment tyexpr
