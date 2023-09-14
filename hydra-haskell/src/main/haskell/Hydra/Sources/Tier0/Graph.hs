{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier0.Graph where

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

import Hydra.Sources.Tier0.Compute


hydraGraphModule :: Module Kv
hydraGraphModule = Module ns elements [hydraComputeModule] $
    Just "The extension to graphs of Hydra's core type system (hydra/core)"
  where
    ns = Namespace "hydra/graph"
    core = typeref $ moduleNamespace hydraCoreModule
    compute = typeref $ moduleNamespace hydraComputeModule
    graph = typeref ns
    def = datatype ns

    elements = [

      def "AnnotationClass" $
        doc "A typeclass-like construct providing common functions for working with annotations" $
        lambda "a" $ record [
          "default">: "a",
          "equal">: "a" --> "a" --> boolean,
          "compare">: "a" --> "a" --> graph "Comparison",
          "show">: "a" --> string,
          "read">: string --> optional "a",

          -- TODO: simplify
          "termAnnotation">:
            core "Term" @@ "a" --> "a",
          "typeAnnotation">:
            core "Type" @@ "a" --> "a",
          "termDescription">:
            core "Term" @@ "a" --> compute "Flow" @@ (graph "Graph" @@ "a") @@ optional string,
          "typeDescription">:
            core "Type" @@ "a" --> compute "Flow" @@ (graph "Graph" @@ "a") @@ optional string,
          "typeClasses">:
            core"Type" @@ "a" --> compute "Flow" @@ (graph "Graph" @@ "a") @@ (Types.map (core "Name") (set $ graph "TypeClass")),
          "termType">:
            core "Term" @@ "a" --> compute "Flow" @@ (graph "Graph" @@ "a") @@ optional (core "Type" @@ "a"),
          "setTermDescription">:
            optional string --> core "Term" @@ "a" --> core "Term" @@ "a",
          "setTermType">:
            optional (core "Type" @@ "a") --> core "Term" @@ "a" --> core "Term" @@ "a",
          "setTypeClasses">:
            (Types.map (core "Name") (set $ graph "TypeClass")) --> core "Type" @@ "a" --> core "Type" @@ "a",
          "typeOf">:
            "a" --> compute "Flow" @@ (graph "Graph" @@ "a") @@ optional (core "Type" @@ "a"),
          "setTypeOf">:
            optional (core "Type" @@ "a") --> "a" --> "a"],

      def "Comparison" $
        doc "An equality judgement: less than, equal to, or greater than" $
        enum [
          "lessThan",
          "equalTo",
          "greaterThan"],

      def "Graph" $
        doc "A graph, or set of name/term bindings together with parameters (annotations, primitives) and a schema graph" $
        lambda "a" $ record [

          -- TODO: remove this; replace it with 'environment'
          "elements">:
            doc "All of the elements in the graph" $
            Types.map (core "Name") (graph "Element" @@ "a"),

          "environment">:
            doc "The lambda environment of this graph context; it indicates whether a variable is bound by a lambda (Nothing) or a let (Just term)" $
            Types.map (core "Name") (optional $ core "Term" @@ "a"),
          "types">:
            doc "The typing environment of the graph" $
            Types.map (core "Name") (core "Type" @@ "a"),
          "body">:
            doc "The body of the term which generated this context" $
            core "Term" @@ "a",
          "primitives">:
            doc "All supported primitive constants and functions, by name" $
            Types.map (core "Name") (graph "Primitive" @@ "a"),
          "annotations">:
            doc "The annotation class which is supported in this context" $
            graph "AnnotationClass" @@ "a",
          "schema">:
            doc "The schema of this graph. If this parameter is omitted (nothing), the graph is its own schema graph." $
            optional $ graph "Graph" @@ "a"],

      def "Element" $
        doc "A graph element, having a name, data term (value), and schema term (type)" $
        lambda "a" $ record [
          "name">: core "Name",
          "data">: core "Term" @@ "a"],

      def "Primitive" $
        doc "A built-in function" $
        lambda "a" $ record [
          "name">:
            doc "The unique name of the primitive function" $
            core "Name",
          "type">:
            doc "The type signature of the primitive function" $
            core "Type" @@ "a",
          "implementation">:
            doc "A concrete implementation of the primitive function" $
            list (core "Term" @@ "a") --> compute "Flow" @@ (graph "Graph" @@ "a") @@ (core "Term" @@ "a")],

      def "TermCoder" $
        doc "A type together with a coder for mapping terms into arguments for primitive functions, and mapping computed results into terms" $
        lambda "a" $ lambda "x" $ record [
          "type">: core "Type" @@ "a",
          "coder">: compute "Coder" @@ (graph "Graph" @@ "a") @@ (graph "Graph" @@ "a") @@ (core "Term" @@ "a") @@ "x"],

      def "TypeClass" $
        doc "Any of a small number of built-in type classes" $
        enum [
          "equality",
          "ordering"]]
