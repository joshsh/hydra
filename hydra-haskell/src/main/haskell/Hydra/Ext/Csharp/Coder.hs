module Hydra.Ext.Csharp.Coder (moduleToCsharp) where

import Hydra.Kernel
import Hydra.Adapters
import Hydra.Ext.Csharp.Language
import qualified Hydra.Ext.Csharp.Syntax as Cs
import Hydra.Ext.Csharp.Utils
import Hydra.Ext.Csharp.Serde
import Hydra.Dsl.Terms
import Hydra.Tools.Serialization
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


data CsharpEnvironment = CsharpEnvironment {} deriving Show

encodeDefinition :: CsharpEnvironment -> Definition -> Flow Graph [Cs.NamespaceMemberDeclaration]
encodeDefinition env def = case def of
  DefinitionTerm name term typ -> withTrace ("data element " ++ unName name) $
    return [] -- TODO
  DefinitionType name typ -> withTrace ("type element " ++ unName name) $ do
    comment <- fmap normalizeComment <$> getTypeDescription typ
    encodeTypeAssignment env name typ comment

encodeModule :: Module -> Flow Graph Cs.CompilationUnit
encodeModule mod = do
    defs <- adaptedModuleDefinitions csharpLanguage mod
    let env = CsharpEnvironment {}
    return $ Cs.CompilationUnit externs usings attributes members
  where
    externs = []
    usings = []
    attributes = []
    members = []

encodeTypeAssignment :: CsharpEnvironment -> Name -> Type -> Maybe String -> Flow Graph [Cs.NamespaceMemberDeclaration]
encodeTypeAssignment env name typ comment = pure []

moduleToCsharp :: Module -> Flow Graph (M.Map FilePath String)
moduleToCsharp mod = do
  comp <- encodeModule mod
  fail "Not implemented"
--  let s = printExpr $ parenthesize $ encodeModule file
--  let path = namespaceToFilePath False (FileExtension "py") $ moduleNamespace mod
--  return $ M.fromList [(path, s)]