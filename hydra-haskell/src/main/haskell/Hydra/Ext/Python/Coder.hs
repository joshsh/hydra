module Hydra.Ext.Python.Coder (moduleToPython) where

import Hydra.Kernel
import Hydra.Adapters
import Hydra.Ext.Python.Language
import Hydra.Dsl.Terms
import Hydra.Tools.Serialization
import qualified Hydra.Ext.Python.Syntax as Py
import Hydra.Ext.Python.Utils
import Hydra.Ext.Python.Serde hiding (encodeName, encodeTerm)
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

    importStmts = simpleStatementNoComment . toImport <$> pairs
      where
        pairs = [
          ("typing", ["List", "NewType", "Optional"]),
          ("dataclasses", ["dataclass"])]
        toImport (modName, symbols) = Py.SimpleStatementImport $ Py.ImportStatementFrom $
          Py.ImportFrom [] (Just $ Py.DottedName [Py.Name modName]) $
            Py.ImportFromTargetsSimple (forSymbol <$> symbols)
          where
            forSymbol s = Py.ImportFromAsName (Py.Name s) Nothing

encodeFieldType :: PythonNamespaces -> FieldType -> Flow Graph Py.StatementWithComment
encodeFieldType namespaces (FieldType fname ftype) = do
  comments <- getTypeDescription ftype
  let pyName = Py.SingleTargetName $ Py.Name $ unName fname
  pyType <- encodeType namespaces ftype
  let stmt = pyAssignmentToPyStatement $ Py.AssignmentTyped $ Py.TypedAssignment pyName pyType Nothing
  return $ Py.StatementWithComment stmt comments

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

encodeName :: PythonNamespaces -> Name -> Flow Graph Py.Name
encodeName namespaces name = pure $ Py.Name $ localNameOfEager name -- TODO: qualified names

encodeRecordType :: PythonNamespaces -> Name -> RowType -> Flow Graph Py.Statement
encodeRecordType namespaces name (RowType tname tfields) = do
    pyFields <- CM.mapM (encodeFieldType namespaces) tfields
    let body = Py.BlockIndented pyFields
    return $ Py.StatementCompound $ Py.CompoundStatementClassDef $ Py.ClassDefinition (Just decs) $
      Py.ClassDefRaw (Py.Name lname) tparams args body
  where
    lname = localNameOfEager name
    tparams = Nothing
    args = Nothing
    decs = Py.Decorators [pyNameToPyNamedExpression $ Py.Name "dataclass"]

encodeTerm :: PythonNamespaces -> Term -> Flow Graph Py.Expression
encodeTerm namespaces term = fail "not yet implemented"

encodeType :: PythonNamespaces -> Type -> Flow Graph Py.Expression
encodeType namespaces typ = case stripType typ of
  TypeList et -> singleParamType (Py.Name "list") <$> encodeType namespaces et
  TypeLiteral lt -> encodeLiteralType lt
  TypeOptional et -> singleParamType (Py.Name "Optional") <$> encodeType namespaces et
  TypeVariable name -> pyNameToPyExpression <$> encodeName namespaces name
  t -> pure $ stringToPyExpression $ "type = " ++ show t
  where
    singleParamType pyName param = pyPrimaryToPyExpression $
      primaryWithSlice (pyNameToPyPrimary pyName) $ Py.SliceNamed $ Py.NamedExpressionSimple param

encodeTypeAssignment :: PythonNamespaces -> Name -> Type -> Flow Graph Py.Statement
encodeTypeAssignment namespaces name typ = case stripType typ of
    TypeLiteral lt -> newtypeDeclaration <$> encodeLiteralType lt
    TypeRecord rt -> encodeRecordType namespaces name rt
    TypeUnion _ -> pure dflt
    t -> unexpected "Python-supported type" $ show (typeVariant t)
  where
    dflt = Py.StatementSimple [Py.SimpleStatementBreak] -- TODO
    newtypeDeclaration expr = pyAssignmentToPyStatement $ Py.AssignmentUntyped $ Py.UntypedAssignment
        [Py.StarTargetUnstarred $ Py.TargetWithStarAtomAtom $ Py.StarAtomName $ Py.Name lname]
        rhs
        Nothing
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
