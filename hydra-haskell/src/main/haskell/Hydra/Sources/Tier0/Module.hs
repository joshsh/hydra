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
import           Hydra.Sources.Core

import Hydra.Sources.Tier0.Graph


hydraModuleModule :: Module
hydraModuleModule = Module ns elements [hydraGraphModule] [hydraCoreModule] $
    Just "A model for Hydra namespaces and modules"
  where
    ns = Namespace "hydra/module"
    graph = typeref $ moduleNamespace hydraGraphModule
    mod = typeref ns
    def = datatype ns

    elements = [

      def "FileExtension" $
        doc "A file extension (without the dot), e.g. \"json\" or \"py\"" $
        wrap string,

      def "Library" $
        doc "A library of primitive functions" $
        record [
          "namespace">:
            doc "A common prefix for all primitive function names in the library" $
            mod "Namespace",
          "prefix">:
            doc "A preferred namespace prefix for function names in the library"
            string,
          "primitives">:
            doc "The primitives defined in this library" $
            list $ graph "Primitive"],

      def "Module" $
        doc "A logical collection of elements in the same namespace, having dependencies on zero or more other modules" $
        record [
          "namespace">:
            doc "A common prefix for all element names in the module" $
            mod "Namespace",
          "elements">:
            doc "The elements defined in this module" $
            list $ graph "Element",
          "termDependencies">:
            doc "Any modules which the term expressions of this module directly depend upon" $
            list $ mod "Module",
          "typeDependencies">:
            doc "Any modules which the type expressions of this module directly depend upon" $
            list $ mod "Module",
          "description">:
            doc "An optional human-readable description of the module" $
            optional string],

      def "Namespace" $
        doc "A prefix for element names" $
        wrap string,

      def "QualifiedName" $
        doc "A qualified name consisting of an optional namespace together with a mandatory local name" $
        record [
          "namespace">: optional $ mod "Namespace",
          "local">: string]]
