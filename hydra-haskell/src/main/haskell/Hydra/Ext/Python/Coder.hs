module Hydra.Ext.Python.Coder (moduleToPython) where

import Hydra.Kernel
import Hydra.Adapters
import Hydra.Ext.Python.Language
import Hydra.Dsl.Terms
import Hydra.Tools.Serialization
import qualified Hydra.Ext.Python.Syntax as Py
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Dsl.Types as Types
import Hydra.Dsl.ShorthandTypes
import Hydra.Lib.Io
import Hydra.Tools.Formatting
import qualified Hydra.Decode as Decode
import Hydra.Ext.Python.Serde

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y
import Hydra.Rewriting (removeTypeAnnotations, removeTermAnnotations)


type PythonNamespaces = Namespaces String

-- TODO: use these
constantForFieldName tname fname = toUpperCase (localNameOfEager tname) ++ "_" ++ toUpperCase (unName fname)
constantForTypeName tname = toUpperCase $ localNameOfEager tname

constructModule :: PythonNamespaces
  -> Module
  -> M.Map Type (Coder Graph Graph Term Py.Expression)
  -> [(Element, TypedTerm)] -> Flow Graph Py.File
constructModule namespaces mod coders pairs = do
    g <- getState
    stmts <- L.concat <$> CM.mapM (createDeclarations g) pairs
    let mc = moduleDescription mod
    return $ Py.File stmts mc
  where
    createDeclarations g pair@(el, TypedTerm term typ) = if isType typ
      then toTypeDeclarations namespaces el term
      else toDataDeclarations coders namespaces pair

    imports = domainImports ++ standardImports
      where
        domainImports = [] -- TODO
        standardImports = [] -- TODO

encodeLiteralType :: LiteralType -> Py.Expression
encodeLiteralType lt = Py.ExpressionSimple $ Py.Disjunction [Py.Conjunction [
    Py.InversionSimple $ Py.Comparison (Py.BitwiseOr Nothing $ Py.BitwiseXor Nothing $
      Py.BitwiseAnd Nothing (Py.ShiftExpression Nothing $ Py.Sum Nothing $ Py.Term Nothing $ Py.FactorSimple $
        Py.Power (Py.AwaitPrimary False $ Py.PrimaryAtom $ Py.AtomName name) Nothing)) []]]
  where
    name = Py.Name $ show lt -- TODO

encodeTerm :: PythonNamespaces -> Term -> Flow Graph Py.Expression
encodeTerm namespaces term = fail "not yet implemented"

encodeTypeAssignment :: PythonNamespaces -> Name -> Type -> Flow Graph Py.Statement
encodeTypeAssignment namespaces name typ = case stripType typ of
    TypeLiteral lt -> pure $ simpleAssignment $ encodeLiteralType lt
    TypeRecord _ -> pure dflt
    TypeUnion _ -> pure dflt
    t -> unexpected "Python-supported type" $ show (typeVariant t)
  where
    dflt = Py.StatementSimple [Py.SimpleStatementBreak] -- TODO
    simpleAssignment expr = Py.StatementSimple [Py.SimpleStatementAssignment $ Py.AssignmentUntyped $
      Py.UntypedAssignment
        [Py.StarTargetUnstarred $ Py.TargetWithStarAtomAtom $ Py.StarAtomName $ Py.Name (localNameOfEager name)]
        (Py.AnnotatedRhsStar [Py.StarExpressionSimple expr])
        Nothing]

moduleToPythonModule :: Module -> Flow Graph Py.File
moduleToPythonModule mod = do
  namespaces <- namespacesForModule mod
  transformModule pythonLanguage (encodeTerm namespaces) (constructModule namespaces) mod

moduleToPython :: Module -> Flow Graph (M.Map FilePath String)
moduleToPython mod = do
  file <- moduleToPythonModule mod
  let s = printExpr $ parenthesize $ encodeFile file
--  fail $ "namespace = " ++ show (moduleNamespace mod)
  let path = namespaceToFilePath False (FileExtension "py") $ moduleNamespace mod
--  fail $ "path = " ++ path
  return $ M.fromList [(path, s)]

toDataDeclarations :: M.Map Type (Coder Graph Graph Term Py.Expression) -> PythonNamespaces -> (Element, TypedTerm)
  -> Flow Graph [Py.StatementWithComment]
toDataDeclarations coders namespaces (el, TypedTerm term typ) = withTrace ("data element " ++ unName (elementName el)) $ do
  comments <- getTermDescription term
  let stmt = Py.StatementSimple [Py.SimpleStatementContinue] -- TODO
  return [Py.StatementWithComment stmt comments]

namespacesForModule :: Module -> Flow Graph PythonNamespaces
namespacesForModule mod = pure $ Namespaces (moduleNamespace mod, "unknown namespace") M.empty -- TODO

toTypeDeclarations :: PythonNamespaces -> Element -> Term
  -> Flow Graph [Py.StatementWithComment]
toTypeDeclarations namespaces el term = withTrace ("type element " ++ unName name) $ do
    typ <- coreDecodeType term
    comments <- getTypeDescription typ
    stmt <- encodeTypeAssignment namespaces name typ
    return [Py.StatementWithComment stmt comments]
  where
    name = elementName el
