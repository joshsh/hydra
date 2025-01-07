module Hydra.Ext.Python.Coder (moduleToPython) where

import Hydra.Kernel
import Hydra.Adapters
import Hydra.Ext.Python.Language
import Hydra.Dsl.Terms
import Hydra.Tools.Serialization
import qualified Hydra.Ext.Python.Syntax as Py
import Hydra.Ext.Python.Utils
import Hydra.Ext.Python.Serde hiding (encodeTerm)
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Dsl.Types as Types
import Hydra.Dsl.ShorthandTypes
import Hydra.Lib.Io
import Hydra.Tools.Formatting
import qualified Hydra.Decode as Decode

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
    declStmts <- L.concat <$> CM.mapM (createDeclarations g) pairs
    let stmts = importStmts ++ declStmts
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

    importStmts = simpleStatementNoComment <$> [Py.SimpleStatementImport $ Py.ImportStatementFrom $
      Py.ImportFrom [] (Just $ Py.DottedName [Py.Name "typing"]) $
        Py.ImportFromTargetsSimple [Py.ImportFromAsName (Py.Name "NewType") Nothing]]

encodeLiteralType :: LiteralType -> Flow Graph Py.Expression
encodeLiteralType lt = do
    name <- Py.Name <$> findName
    return $ pyNameToPyExpression name
  where
    findName = case lt of
      LiteralTypeBinary -> pure "bytes"
      LiteralTypeBoolean -> pure "bool"
      LiteralTypeFloat ft -> case ft of
        FloatTypeBigfloat -> pure "float"
        _ -> fail $ "unsupported floating-point type: " ++ show ft
      LiteralTypeInteger it -> case it of
        IntegerTypeBigint -> pure "int"
        _ -> fail $ "unsupported integer type: " ++ show it
      LiteralTypeString -> pure "str"

encodeTerm :: PythonNamespaces -> Term -> Flow Graph Py.Expression
encodeTerm namespaces term = fail "not yet implemented"

encodeTypeAssignment :: PythonNamespaces -> Name -> Type -> Flow Graph Py.Statement
encodeTypeAssignment namespaces name typ = case stripType typ of
    TypeLiteral lt -> newtypeDeclaration <$> encodeLiteralType lt
    TypeRecord _ -> pure dflt
    TypeUnion _ -> pure dflt
    t -> unexpected "Python-supported type" $ show (typeVariant t)
  where
    dflt = Py.StatementSimple [Py.SimpleStatementBreak] -- TODO
    newtypeDeclaration expr = Py.StatementSimple [Py.SimpleStatementAssignment $ Py.AssignmentUntyped $
        Py.UntypedAssignment
          [Py.StarTargetUnstarred $ Py.TargetWithStarAtomAtom $ Py.StarAtomName $ Py.Name lname]
          rhs
          Nothing]
      where
        lname = localNameOfEager name
        rhs = Py.AnnotatedRhsStar [Py.StarExpressionSimple $
          functionCall (pyNameToPyPrimary $ Py.Name "NewType") [stringToPyExpression lname, expr]]

moduleToPythonModule :: Module -> Flow Graph Py.File
moduleToPythonModule mod = do
  namespaces <- namespacesForModule mod
  transformModule pythonLanguage (encodeTerm namespaces) (constructModule namespaces) mod

moduleToPython :: Module -> Flow Graph (M.Map FilePath String)
moduleToPython mod = do
  file <- moduleToPythonModule mod
  let s = printExpr $ parenthesize $ encodeFile file
  let path = namespaceToFilePath False (FileExtension "py") $ moduleNamespace mod
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
