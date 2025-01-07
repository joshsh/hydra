module Hydra.Ext.Python.Utils where

import qualified Hydra.Ext.Python.Syntax as Py


pyNameToPyExpression :: Py.Name -> Py.Expression
pyNameToPyExpression =  pyPrimaryToPyExpression . pyNameToPyPrimary

pyNameToPyPrimary :: Py.Name -> Py.Primary
pyNameToPyPrimary = Py.PrimarySimple . Py.AtomName

pyPrimaryToPyExpression :: Py.Primary -> Py.Expression
pyPrimaryToPyExpression prim = Py.ExpressionSimple $ Py.Disjunction [Py.Conjunction [
  Py.InversionSimple $ Py.Comparison (Py.BitwiseOr Nothing $ Py.BitwiseXor Nothing $
    Py.BitwiseAnd Nothing (Py.ShiftExpression Nothing $ Py.Sum Nothing $ Py.Term Nothing $ Py.FactorSimple $
      Py.Power (Py.AwaitPrimary False prim) Nothing)) []]]

functionCall :: Py.Primary -> [Py.Expression] -> Py.Expression
functionCall func args = pyPrimaryToPyExpression $ Py.PrimaryCompound $ Py.PrimaryWithRhs func $
  Py.PrimaryRhsCall $ Py.Args (Py.PosArgExpression <$> args) [] []

simpleStatementNoComment :: Py.SimpleStatement -> Py.StatementWithComment
simpleStatementNoComment s = Py.StatementWithComment (Py.StatementSimple [s]) Nothing


stringToPyExpression :: String -> Py.Expression
stringToPyExpression = pyPrimaryToPyExpression . Py.PrimarySimple . Py.AtomString