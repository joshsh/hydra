module Hydra.Ext.Python.Serde where

import qualified Hydra.Ext.Python.Syntax as Py
import Hydra.Tools.Serialization
import qualified Hydra.Ast as A

import qualified Data.List as L
import qualified Data.Maybe as Y


encodeAnnotatedRhs :: Py.AnnotatedRhs -> A.Expr
encodeAnnotatedRhs a = case a of
  Py.AnnotatedRhsStar s -> commaSep inlineStyle (encodeStarExpression <$> s)
  _ -> cst "[other annotated rhs]"

encodeAssignment :: Py.Assignment -> A.Expr
encodeAssignment a = case a of
  Py.AssignmentUntyped u -> encodeUntypedAssignment u
  _ -> cst "[other assignment]"

encodeAtom :: Py.Atom -> A.Expr
encodeAtom a = case a of
  Py.AtomName n -> encodeName n
  _ -> cst "[other atom]"

encodeComparison :: Py.Comparison -> A.Expr
encodeComparison c = cst "[comparison]"

encodeCompoundStatement :: Py.CompoundStatement -> A.Expr
encodeCompoundStatement c = cst "[compound statement]"

encodeConjunction :: Py.Conjunction -> A.Expr
encodeConjunction (Py.Conjunction is) = symbolSep "and" inlineStyle (encodeInversion <$> is)

encodeDisjunction :: Py.Disjunction -> A.Expr
encodeDisjunction (Py.Disjunction cs) = symbolSep "or" inlineStyle (encodeConjunction <$> cs)

encodeExpression :: Py.Expression -> A.Expr
encodeExpression e = case e of
  Py.ExpressionSimple d -> encodeDisjunction d
  _ -> cst "[other expression]"

encodeFile :: Py.File -> A.Expr
encodeFile (Py.File stmts mdoc) = doubleNewlineSep $ Y.catMaybes $
   [cst . toPythonComments <$> mdoc] ++ stmtExprs
  where
    stmtExprs = Just . encodeStatementWithComment <$> stmts

encodeInversion :: Py.Inversion -> A.Expr
encodeInversion i = case i of
    Py.InversionNot other -> spaceSep [cst "not", encodeInversion other]
    Py.InversionSimple c -> encodeComparison c

encodeName :: Py.Name -> A.Expr
encodeName (Py.Name n) = cst n

encodeSimpleStatement :: Py.SimpleStatement -> A.Expr
encodeSimpleStatement s = case s of
  Py.SimpleStatementAssignment a -> encodeAssignment a
  _ -> cst "[other simple statement]"

encodeStarAtom :: Py.StarAtom -> A.Expr
encodeStarAtom a = case a of
  Py.StarAtomName n -> encodeName n
  _ -> cst "[other star atom]"

encodeStarExpression :: Py.StarExpression -> A.Expr
encodeStarExpression s = case s of
  Py.StarExpressionSimple e -> encodeExpression e
  _ -> cst "[other star expression]"

encodeStarTarget :: Py.StarTarget -> A.Expr
encodeStarTarget s = case s of
  Py.StarTargetUnstarred t -> encodeTargetWithStarAtom t
  _ -> cst "[other star target]"

encodeStatement :: Py.Statement -> A.Expr
encodeStatement s = case s of
  Py.StatementCompound c -> encodeCompoundStatement c
  Py.StatementSimple stmts -> newlineSep (encodeSimpleStatement <$> stmts)

encodeStatementWithComment :: Py.StatementWithComment -> A.Expr
encodeStatementWithComment (Py.StatementWithComment stmt mdoc) = newlineSep $ Y.catMaybes $
  [cst . toPythonComments <$> mdoc, Just $ encodeStatement stmt]

encodeTargetWithStarAtom :: Py.TargetWithStarAtom -> A.Expr
encodeTargetWithStarAtom t = case t of
  Py.TargetWithStarAtomAtom a -> encodeStarAtom a
  _ -> cst "[other target with star atom]"

encodeUntypedAssignment :: Py.UntypedAssignment -> A.Expr
encodeUntypedAssignment (Py.UntypedAssignment targets rhs _) = spaceSep $ lefts ++ [right]
  where
    lefts = encodeTarget <$> targets
    right = encodeAnnotatedRhs rhs
    encodeTarget t = spaceSep [encodeStarTarget t, cst "="]

toPythonComments :: String -> String
toPythonComments c = L.intercalate "\n" $ ("# " ++) <$> L.lines c
