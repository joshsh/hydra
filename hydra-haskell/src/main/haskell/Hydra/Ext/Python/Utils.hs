module Hydra.Ext.Python.Utils where

import Hydra.Tools.Formatting
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
    primaryWithExpressionSlices (pyNameToPyPrimary $ Py.Name "Annotated")
    [expr, doubleQuotedString c]

annotatedStatement :: Maybe String -> Py.Statement -> Py.Statement
annotatedStatement mcomment stmt = case mcomment of
  Nothing -> stmt
  Just c -> Py.StatementAnnotated $ Py.AnnotatedStatement c stmt

commentStatement :: String -> Py.Statement
commentStatement = pyExpressionToPyStatement . tripleQuotedString

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

doubleQuotedString :: String -> Py.Expression
doubleQuotedString = stringToPyExpression Py.QuoteStyleDouble

functionCall :: Py.Primary -> [Py.Expression] -> Py.Expression
functionCall func args = pyPrimaryToPyExpression $ primaryWithRhs func $
  Py.PrimaryRhsCall $ Py.Args (Py.PosArgExpression <$> args) [] []

indentedBlock :: Maybe String -> [[Py.Statement]] -> Py.Block
indentedBlock mcomment stmts = if L.null groups
    then Py.BlockSimple [pyExpressionToPySimpleStatement $ pyAtomToPyExpression Py.AtomEllipsis]
    else Py.BlockIndented groups
  where
    commentGroup = case mcomment of
      Just s -> [commentStatement s]
      Nothing -> []
    groups = L.filter (not . L.null) $ (commentGroup:stmts)

nameAndParams :: Py.Name -> [Py.Expression] -> Py.Expression
nameAndParams pyName params = primaryAndParams (pyNameToPyPrimary pyName) params

newtypeStatement :: Py.Name -> Maybe String -> Py.Expression -> Py.Statement
newtypeStatement name mcomment expr = annotatedStatement mcomment $ assignmentStatement name $
  functionCall (pyNameToPyPrimary $ Py.Name "NewType") [doubleQuotedString $ Py.unName name, expr]

normalizeComment :: String -> String
normalizeComment s = if L.null stripped
    then ""
    else if L.last stripped /= '.'
      then stripped ++ "."
      else stripped
  where
    stripped = stripLeadingAndTrailingWhitespace s

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

pyClassDefinitionToPyStatement :: Py.ClassDefinition -> Py.Statement
pyClassDefinitionToPyStatement = Py.StatementCompound . Py.CompoundStatementClassDef

pyConjunctionToPyExpression :: Py.Conjunction -> Py.Expression
pyConjunctionToPyExpression conj = Py.ExpressionSimple $ Py.Disjunction [conj]

-- Extracts the primary from an expression, or wraps it in parentheses if the expression does not contain a primary.
pyExpressionToPyPrimary :: Py.Expression -> Py.Primary
pyExpressionToPyPrimary e = case decodePyExpressionToPyPrimary e of
  Just prim -> prim
  Nothing -> Py.PrimarySimple $ Py.AtomGroup $ Py.GroupExpression $ Py.NamedExpressionSimple e

pyExpressionToPyAnnotatedRhs :: Py.Expression -> Py.AnnotatedRhs
pyExpressionToPyAnnotatedRhs expr = Py.AnnotatedRhsStar [Py.StarExpressionSimple expr]

pyExpressionsToPyArgs :: [Py.Expression] -> Py.Args
pyExpressionsToPyArgs exprs = Py.Args (Py.PosArgExpression <$> exprs) [] []

pyExpressionToPySlice :: Py.Expression -> Py.Slice
pyExpressionToPySlice = Py.SliceNamed . Py.NamedExpressionSimple

pyExpressionToPySimpleStatement :: Py.Expression -> Py.SimpleStatement
pyExpressionToPySimpleStatement expr = Py.SimpleStatementStarExpressions [Py.StarExpressionSimple expr]

pyExpressionToPyStatement :: Py.Expression -> Py.Statement
pyExpressionToPyStatement = pySimpleStatementToPyStatement . pyExpressionToPySimpleStatement

pyList :: [Py.Expression] -> Py.List
pyList exprs = Py.List (Py.StarNamedExpressionSimple . Py.NamedExpressionSimple <$> exprs)

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

pyNone :: Py.Name
pyNone = Py.Name "None"

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

stringToPyExpression :: Py.QuoteStyle -> String -> Py.Expression
stringToPyExpression style s = pyAtomToPyExpression $ Py.AtomString $ Py.String_ s style

tripleQuotedString :: String -> Py.Expression
tripleQuotedString = stringToPyExpression Py.QuoteStyleTriple

typeAliasStatement :: Py.Name -> [Py.TypeParameter] -> Maybe String -> Py.Expression -> Py.Statement
typeAliasStatement name tparams mcomment tyexpr = annotatedStatement mcomment $
 pySimpleStatementToPyStatement $ Py.SimpleStatementTypeAlias $ Py.TypeAlias name tparams tyexpr
