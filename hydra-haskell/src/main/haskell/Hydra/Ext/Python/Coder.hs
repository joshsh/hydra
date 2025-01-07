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
    decls <- L.concat <$> CM.mapM (createDeclarations g) pairs
    let mc = moduleDescription mod
    return $ Py.File []
  where
    createDeclarations g pair@(el, TypedTerm term typ) = do
      if isType typ
        then toTypeDeclarations namespaces el term
        else toDataDeclarations coders namespaces pair

    imports = domainImports ++ standardImports
      where
        domainImports = [] -- TODO
        standardImports = [] -- TODO

encodeTerm :: PythonNamespaces -> Term -> Flow Graph Py.Expression
encodeTerm namespaces term = fail "not yet implemented"

moduleToPythonModule :: Module -> Flow Graph Py.File
moduleToPythonModule mod = do
    namespaces <- namespacesForModule mod
    transformModule pythonLanguage (encodeTerm namespaces) (constructModule namespaces) mod

moduleToPython :: Module -> Flow Graph (M.Map FilePath String)
moduleToPython mod = do
  file <- moduleToPythonModule mod
  let s = printExpr $ parenthesize $ encodeFile file
  return $ M.fromList [(namespaceToFilePath True (FileExtension "py") $ moduleNamespace mod, s)]

toDataDeclarations :: M.Map Type (Coder Graph Graph Term Py.Expression) -> PythonNamespaces -> (Element, TypedTerm)
  -> Flow Graph [Py.Statement]
toDataDeclarations coders namespaces (el, TypedTerm term typ) = withTrace ("data element " ++ unName (elementName el)) $ do
  return [Py.StatementSimple [Py.SimpleStatementContinue]]

namespacesForModule :: Module -> Flow Graph PythonNamespaces
namespacesForModule mod = fail "TODO"

toTypeDeclarations :: PythonNamespaces -> Element -> Term
  -> Flow Graph [Py.Statement]
toTypeDeclarations namespaces el term = withTrace ("type element " ++ unName (elementName el)) $ do
  return [Py.StatementSimple [Py.SimpleStatementBreak]]
