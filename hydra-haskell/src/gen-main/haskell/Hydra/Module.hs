-- | A model for Hydra namespaces and modules

module Hydra.Module where

import qualified Hydra.Core as Core
import qualified Hydra.Graph as Graph
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

newtype FileExtension = 
  FileExtension {
    unFileExtension :: String}
  deriving (Eq, Ord, Read, Show)

_FileExtension = (Core.Name "hydra/module.FileExtension")

-- | A library of primitive functions
data Library = 
  Library {
    -- | A common prefix for all primitive function names in the library
    libraryNamespace :: Namespace,
    -- | A preferred namespace prefix for function names in the library
    libraryPrefix :: String,
    -- | The primitives defined in this library
    libraryPrimitives :: [Graph.Primitive]}

_Library = (Core.Name "hydra/module.Library")

_Library_namespace = (Core.Name "namespace")

_Library_prefix = (Core.Name "prefix")

_Library_primitives = (Core.Name "primitives")

-- | A logical collection of elements in the same namespace, having dependencies on zero or more other modules
data Module = 
  Module {
    -- | A common prefix for all element names in the module
    moduleNamespace :: Namespace,
    -- | The elements defined in this module
    moduleElements :: [Graph.Element],
    -- | Any modules which the term expressions of this module directly depend upon
    moduleTermDependencies :: [Module],
    -- | Any modules which the type expressions of this module directly depend upon
    moduleTypeDependencies :: [Module],
    -- | An optional human-readable description of the module
    moduleDescription :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Module = (Core.Name "hydra/module.Module")

_Module_namespace = (Core.Name "namespace")

_Module_elements = (Core.Name "elements")

_Module_termDependencies = (Core.Name "termDependencies")

_Module_typeDependencies = (Core.Name "typeDependencies")

_Module_description = (Core.Name "description")

-- | A prefix for element names
newtype Namespace = 
  Namespace {
    unNamespace :: String}
  deriving (Eq, Ord, Read, Show)

_Namespace = (Core.Name "hydra/module.Namespace")

-- | A qualified name consisting of an optional namespace together with a mandatory local name
data QualifiedName = 
  QualifiedName {
    qualifiedNameNamespace :: (Maybe Namespace),
    qualifiedNameLocal :: String}
  deriving (Eq, Ord, Read, Show)

_QualifiedName = (Core.Name "hydra/module.QualifiedName")

_QualifiedName_namespace = (Core.Name "namespace")

_QualifiedName_local = (Core.Name "local")