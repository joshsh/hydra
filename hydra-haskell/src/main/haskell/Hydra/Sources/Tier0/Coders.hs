{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier0.Coders where

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

import Hydra.Sources.Tier0.Compute
import Hydra.Sources.Tier0.Graph
import Hydra.Sources.Tier0.Mantle


hydraCodersModule :: Module
hydraCodersModule = Module ns elements [hydraCoreModule, hydraMantleModule, hydraComputeModule, hydraGraphModule] $
    Just "Abstractions for paired transformations between languages"
  where
    ns = Namespace "hydra/coders"
    core = typeref $ moduleNamespace hydraCoreModule
    compute = typeref $ moduleNamespace hydraComputeModule
    graph = typeref $ moduleNamespace hydraGraphModule
    mantle = typeref $ moduleNamespace hydraMantleModule
    coders = typeref ns

    def = datatype ns

    elements = [

      def "AdapterContext" $
        doc "An evaluation context together with a source language and a target language" $
        lambda "a" $ record [
          "graph">: apply (graph "Graph") (var "a"),
          "language">: apply (coders "Language") (var "a"),
          "adapters">: Types.map (core "Name") (compute "Adapter"
            @@ (coders "AdapterContext" @@ "a") @@ (coders "AdapterContext" @@ "a")
            @@ (core "Type" @@ "a") @@ (core "Type" @@ "a")
            @@ (core "Term" @@ "a") @@ (core "Term" @@ "a"))],

      def "CoderDirection" $
        doc "Indicates either the 'out' or the 'in' direction of a coder" $
        enum [
          "encode",
          "decode"],

      def "Language" $
        doc "A named language together with language-specific constraints" $
        lambda "a" $ record [
          "name">: coders "LanguageName",
          "constraints">: apply (coders "LanguageConstraints") (var "a")],

      def "LanguageConstraints" $
        doc "A set of constraints on valid type and term expressions, characterizing a language" $
        lambda "a" $ record [
          "eliminationVariants">:
            doc "All supported elimination variants" $
            Types.set $ mantle "EliminationVariant",
          "literalVariants">:
            doc "All supported literal variants" $
            Types.set $ mantle "LiteralVariant",
          "floatTypes">:
            doc "All supported float types" $
            Types.set $ core "FloatType",
          "functionVariants">:
            doc "All supported function variants" $
            Types.set $ mantle "FunctionVariant",
          "integerTypes">:
            doc "All supported integer types" $
            Types.set $ core "IntegerType",
          "termVariants">:
            doc "All supported term variants" $
            Types.set $ mantle "TermVariant",
          "typeVariants">:
            doc "All supported type variants" $
            Types.set $ mantle "TypeVariant",
          "types">:
            doc "A logical set of types, as a predicate which tests a type for inclusion" $
            core "Type" @@ "a" --> boolean],

      def "LanguageName" $
        doc "The unique name of a language" string,

      def "TraversalOrder" $
        doc "Specifies either a pre-order or post-order traversal" $
        union [
          "pre">: doc "Pre-order traversal" unit,
          "post">: doc "Post-order traversal" unit]]
