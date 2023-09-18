{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier0.Module where

-- Standard Tier-0 imports
import qualified Data.List             as L
import qualified Data.Map              as M
import qualified Data.Set              as S
import qualified Data.Maybe            as Y
import           Hydra.Dsl.Annotations
import           Hydra.Dsl.Bootstrap
import qualified Hydra.Dsl.Terms       as Terms
import           Hydra.Dsl.Types       as Types
import           Hydra.Kernel
import           Hydra.Sources.Core

import Hydra.Sources.Tier0.Graph


hydraModuleModule :: Module
hydraModuleModule = Module ns elements [hydraGraphModule] $
    Just "A model for Hydra namespaces and modules (collections of elements in the same namespace)"
  where
    ns = Namespace "hydra/module"
    graph = typeref $ moduleNamespace hydraGraphModule
    mod = typeref ns
    def = datatype ns

    elements = [

      def "FileExtension" string,

      def "Module" $
        doc "A logical collection of elements in the same namespace, having dependencies on zero or more other modules" $
        lambda "a" $ record [
          "namespace">:
            doc "A common prefix for all element names in the module" $
            mod "Namespace",
          "elements">:
            doc "The elements defined in this module" $
            list $ graph "Element" @@ "a",
          "dependencies">:
            doc "Any additional modules this one has a direct dependency upon" $
            list $ mod "Module" @@ "a",
          "description">:
            doc "An optional human-readable description of the module" $
            optional string],

      def "Namespace" $
        doc "A prefix for element names"
        string,

      def "QualifiedName" $
        doc "A qualified name consisting of an optional namespace together with a mandatory local name" $
        record [
          "namespace">: optional $ mod "Namespace",
          "local">: string]]
