module Hydra.Ext.Python.Utils where

import qualified Hydra.Ext.Python.Syntax as Py


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

pyAssignmentToPyStatement :: Py.Assignment -> Py.Statement
pyAssignmentToPyStatement a = Py.StatementSimple [Py.SimpleStatementAssignment a]

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

pyExpressionToPySlice :: Py.Expression -> Py.Slice
pyExpressionToPySlice = Py.SliceNamed . Py.NamedExpressionSimple

pyNameToPyExpression :: Py.Name -> Py.Expression
pyNameToPyExpression =  pyPrimaryToPyExpression . pyNameToPyPrimary

pyNameToPyNamedExpression :: Py.Name -> Py.NamedExpression
pyNameToPyNamedExpression = Py.NamedExpressionSimple . pyNameToPyExpression

pyNameToPyPrimary :: Py.Name -> Py.Primary
pyNameToPyPrimary = Py.PrimarySimple . Py.AtomName

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

functionCall :: Py.Primary -> [Py.Expression] -> Py.Expression
functionCall func args = pyPrimaryToPyExpression $ primaryWithRhs func $
  Py.PrimaryRhsCall $ Py.Args (Py.PosArgExpression <$> args) [] []

orNull :: Py.Expression -> Py.Expression
orNull lhs = pyBitwiseOrToPyExpression $
    Py.BitwiseOr (Just lhsOr) (pyPrimaryToPyBitwiseXor $ pyNameToPyPrimary $ Py.Name "None")
  where
    lhsOr = pyPrimaryToPyBitwiseOr $ pyExpressionToPyPrimary lhs

primaryWithRhs :: Py.Primary -> Py.PrimaryRhs -> Py.Primary
primaryWithRhs prim rhs = Py.PrimaryCompound $ Py.PrimaryWithRhs prim rhs

primaryWithExpressionSlices :: Py.Primary -> [Py.Expression] -> Py.Primary
primaryWithExpressionSlices prim exprs = primaryWithSlices prim
  (pyExpressionToPySlice $ head exprs)
  (Py.SliceOrStarredExpressionSlice . pyExpressionToPySlice <$> tail exprs)

primaryWithSlices :: Py.Primary -> Py.Slice -> [Py.SliceOrStarredExpression] -> Py.Primary
primaryWithSlices prim first rest = primaryWithRhs prim $ Py.PrimaryRhsSlices $ Py.Slices first rest

simpleStatementNoComment :: Py.SimpleStatement -> Py.StatementWithComment
simpleStatementNoComment s = Py.StatementWithComment (Py.StatementSimple [s]) Nothing

stringToPyExpression :: String -> Py.Expression
stringToPyExpression = pyPrimaryToPyExpression . Py.PrimarySimple . Py.AtomString
