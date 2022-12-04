{-# LANGUAGE OverloadedStrings #-}

module Hydra.Impl.Haskell.Sources.Compute where

import Hydra.Kernel
import Hydra.Impl.Haskell.Dsl.Types as Types
import Hydra.Impl.Haskell.Dsl.Standard
import Hydra.Impl.Haskell.Sources.Core
import Hydra.Impl.Haskell.Sources.Mantle


hydraComputeModule :: Module Meta
hydraComputeModule = Module ns elements [hydraMantleModule] $
    Just "Abstractions for evaluation and transformations"
  where
    ns = Namespace "hydra/compute"
    core = nsref $ moduleNamespace hydraCoreModule
    mantle = nsref $ moduleNamespace hydraMantleModule
    compute = nsref ns

    def = datatype ns

    elements = [
      def "Adapter" $
        lambda "s1" $ lambda "s2" $ lambda "t1" $ lambda "t2" $ lambda "v1" $ lambda "v2" $ record [
          "isLossy">: boolean,
          "source">: variable "t1",
          "target">: variable "t2",
          "coder">: compute "Coder" @@ "s1" @@ "s2" @@ "v1" @@ "v2"],

      def "AdapterContext" $
        lambda "m" $ record [
          "evaluation">: apply (compute "Context") (variable "m"),
          "source">: apply (compute "Language") (variable "m"),
          "target">: apply (compute "Language") (variable "m")],

      def "AnnotationClass" $
        doc "A typeclass-like construct providing common functions for working with annotations" $
        lambda "m" $ record [
          "default">: "m",
          "equal">: "m" --> "m" --> boolean,
          "compare">: "m" --> "m" --> mantle "Comparison",
          "show">: "m" --> string,
          "read">: string --> optional "m",

          -- TODO: simplify
          "termMeta">:
            core "Term" @@ "m" --> "m",
          "typeMeta">:
            core "Type" @@ "m" --> "m",
          "termDescription">:
            core "Term" @@ "m" --> compute "Flow" @@ (compute "Context" @@ "m") @@ optional string,
          "typeDescription">:
            core "Type" @@ "m" --> compute "Flow" @@ (compute "Context" @@ "m") @@ optional string,
          "termType">:
            core "Term" @@ "m" --> compute "Flow" @@ (compute "Context" @@ "m") @@ optional (core "Type" @@ "m"),
          "setTermDescription">:
            compute "Context" @@ "m" --> optional string --> core "Term" @@ "m" --> core "Term" @@ "m",
          "setTermType">:
            compute "Context" @@ "m" --> optional (core "Type" @@ "m") --> core "Term" @@ "m" --> core "Term" @@ "m",
          "typeOf">:
            "m" --> compute "Flow" @@ (compute "Context" @@ "m") @@ optional (core "Type" @@ "m"),
          "setTypeOf">:
            optional (core "Type" @@ "m") --> "m" --> "m"],

      def "Coder" $
        doc "An encoder and decoder; a bidirectional flow between two types" $
        lambda "s1" $ lambda "s2" $ lambda "v1" $ lambda "v2" $ record [
          "encode">: ("v1" --> compute "Flow" @@ "s1" @@ "v2"),
          "decode">: ("v2" --> compute "Flow" @@ "s2" @@ "v1")],

      def "CoderDirection" $
        doc "Indicates either the 'out' or the 'in' direction of a coder" $
        enum [
          "encode",
          "decode"],

      def "Context" $
        doc "An environment containing a graph together with primitive functions and other necessary components for evaluation" $
        lambda "m" $ record [
          "graph">: mantle "Graph" @@ "m",
          "functions">: Types.map (core "Name") (compute "PrimitiveFunction" @@ "m"),
          "strategy">: compute "EvaluationStrategy",
          "annotations">: compute "AnnotationClass" @@ "m"],

      def "EvaluationStrategy" $
        doc "Settings which determine how terms are evaluated" $
        record [
          "opaqueTermVariants">: set (mantle "TermVariant")],

      def "Flow" $
        doc "A variant of the State monad with built-in logging and error handling" $
        lambda "s" $ lambda "a" $
        function "s" (compute "Trace" --> compute "FlowState" @@ "s" @@ "a"),

      def "FlowState" $
        lambda "s" $ lambda "a" $ record [
          "value">: optional "a",
          "state">: "s",
          "trace">: compute "Trace"],

      def "Language" $
        lambda "m" $ record [
          "name">: compute "LanguageName",
          "constraints">: apply (compute "LanguageConstraints") (variable "m")],

      def "LanguageConstraints" $
        lambda "m" $ record [
          "eliminationVariants">: Types.set $ mantle "EliminationVariant",
          "literalVariants">: Types.set $ mantle "LiteralVariant",
          "floatTypes">: Types.set $ core "FloatType",
          "functionVariants">: Types.set $ mantle "FunctionVariant",
          "integerTypes">: Types.set $ core "IntegerType",
          "termVariants">: Types.set $ mantle "TermVariant",
          "typeVariants">: Types.set $ mantle "TypeVariant",
          "types">: core "Type" @@ "m" --> boolean],

      def "LanguageName" string,

      def "Meta" $
        doc "A built-in metadata container for terms" $
        record [
          "annotations">:
            doc "A map of annotation names to annotation values" $
            Types.map string (core "Term" @@ compute "Meta")],

      def "PrimitiveFunction" $
        doc "A built-in function" $
        lambda "m" $ record [
          "name">: core "Name",
          "type">: core "FunctionType" @@ "m",
          "implementation">:
            list (core "Term" @@ "m") --> compute "Flow" @@ (compute "Context" @@ "m") @@ (core "Term" @@ "m")],

      def "TermCoder" $
        doc "A type together with a coder for mapping terms into arguments for primitive functions, and mapping computed results into terms" $
        lambda "m" $ lambda "a" $ record [
          "type">: core "Type" @@ "m",
          "coder">: compute "Coder" @@ (compute "Context" @@ "m") @@ (compute "Context" @@ "m") @@ (core "Term" @@ "m") @@ "a"],

      def "Trace" $
        doc "A container for logging and error information" $
        record [
          "stack">: list string,
          "messages">: list string,
          "other">:
            doc "A map of string keys to arbitrary terms as values, for application-specific use" $
            Types.map string (core "Term" @@ compute "Meta")],

      def "TraversalOrder" $
        union [
          "pre">: doc "Pre-order traversal" unit,
          "post">: doc "Post-order traversal" unit]]
