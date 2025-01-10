{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Core(
  hydraCore,
  hydraCoreModule,
  module Hydra.Kernel,
) where

import Hydra.Kernel
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types


hydraCore :: Graph
hydraCore = elementsToGraph bootstrapGraph Nothing (moduleElements hydraCoreModule)

hydraCoreModule :: Module
hydraCoreModule = Module ns elements [] [] $
    Just "Hydra's core data model of type and term expressions"
  where
    ns = Namespace "hydra/core"
    core = typeref ns
    def = datatype ns
    doc s = setTypeDescription (Just s)

    elements = [

      def "AnnotatedTerm" $
        doc "A term together with an annotation" $
        record [
          "subject">: core "Term",
          "annotation">: Types.map (core "Name") $ core "Term"],

      def "AnnotatedType" $
        doc "A type together with an annotation" $
        record [
          "subject">: core "Type",
          "annotation">: Types.map (core "Name") $ core "Term"],

      def "Application" $
        doc "A term which applies a function to an argument" $
        record [
          "function">:
            doc "The left-hand side of the application" $
            core "Term",
          "argument">:
            doc "The right-hand side of the application" $
            core "Term"],

      def "ApplicationType" $
        doc "The type-level analog of an application term" $
        record [
          "function">:
            doc "The left-hand side of the application" $
            core "Type",
          "argument">:
            doc "The right-hand side of the application" $
            core "Type"],

      def "CaseStatement" $
        doc "A union elimination; a case statement" $
        record [
          "typeName">: core "Name",
          "default">: optional (core "Term"),
          "cases">: list $ core "Field"],

      def "Elimination" $
        doc "A corresponding elimination for an introduction term" $
        union [
          "list">:
            doc "Eliminates a list using a fold function; this function has the signature b -> [a] -> b" $
            core "Term",
          "optional">:
            doc "Eliminates an optional term by matching over the two possible cases" $
            core "OptionalCases",
          "product">:
            doc "Eliminates a tuple by projecting the component at a given 0-indexed offset" $
            core "TupleProjection",
          "record">:
            doc "Eliminates a record by projecting a given field" $
            core "Projection",
          "union">:
            doc "Eliminates a union term by matching over the fields of the union. This is a case statement." $
            core "CaseStatement",
          "wrap">:
            doc "Unwrap a wrapped term" $
            core "Name"],

      def "Field" $
        doc "A name/term pair" $
        record [
          "name">: core "Name",
          "term">: core "Term"],

      def "FieldType" $
        doc "A name/type pair" $
        record [
          "name">: core "Name",
          "type">: core "Type"],

      def "FloatType" $
        doc "A floating-point type" $
        enum [
          "bigfloat",
          "float32",
          "float64"],

      def "FloatValue" $
        doc "A floating-point literal value" $
        union [
          "bigfloat">:
            doc "An arbitrary-precision floating-point value" bigfloat,
          "float32">:
            doc "A 32-bit floating-point value" float32,
          "float64">:
            doc "A 64-bit floating-point value" float64],

      def "Function" $
        doc "A function" $
        union [
          "elimination">:
            doc "An elimination for any of a few term variants" $
            core "Elimination",
          "lambda">:
            doc "A function abstraction (lambda)" $
            core "Lambda",
          "primitive">:
            doc "A reference to a built-in (primitive) function" $
            core "Name"],

      def "FunctionType" $
        doc "A function type, also known as an arrow type" $
        record [
          "domain">: core "Type",
          "codomain">: core "Type"],

      def "Injection" $
        doc "An instance of a union type; i.e. a string-indexed generalization of inl() or inr()" $
        record [
          "typeName">: core "Name",
          "field">: core "Field"],

      def "IntegerType" $
        doc "An integer type" $
        enum [
          "bigint",
          "int8",
          "int16",
          "int32",
          "int64",
          "uint8",
          "uint16",
          "uint32",
          "uint64"],

      def "IntegerValue" $
        doc "An integer literal value" $
        union [
          "bigint">:
            doc "An arbitrary-precision integer value" bigint,
          "int8">:
            doc "An 8-bit signed integer value" int8,
          "int16">:
            doc "A 16-bit signed integer value (short value)" int16,
          "int32">:
            doc "A 32-bit signed integer value (int value)" int32,
          "int64">:
            doc "A 64-bit signed integer value (long value)" int64,
          "uint8">:
            doc "An 8-bit unsigned integer value (byte)" uint8,
          "uint16">:
            doc "A 16-bit unsigned integer value" uint16,
          "uint32">:
            doc "A 32-bit unsigned integer value (unsigned int)" uint32,
          "uint64">:
            doc "A 64-bit unsigned integer value (unsigned long)" uint64],

      def "Lambda" $
        doc "A function abstraction (lambda)" $
        record [
          "parameter">:
            doc "The parameter of the lambda" $
            core "Name",
          "domain">:
            doc "An optional domain type for the lambda" $
            optional $ core "Type",
          "body">:
            doc "The body of the lambda" $
            core "Term"],

      def "LambdaType" $
        doc "A type abstraction; the type-level analog of a lambda term" $
        record [
          "parameter">:
            doc "The variable which is bound by the lambda" $
            core "Name",
          "body">:
            doc "The body of the lambda" $
            core "Type"],

      def "Let" $
        doc "A set of (possibly recursive) 'let' bindings together with an environment in which they are bound" $
        record [
          "bindings">: list $ core "LetBinding",
          "environment">: core "Term"],

      def "LetBinding" $
        doc "A field with an optional type scheme, used to bind variables to terms in a 'let' expression" $
        record [
          "name">: core "Name",
          "term">: core "Term",
          "type">: optional $ core "TypeScheme"],

      def "Literal" $
        doc "A term constant; an instance of a literal type" $
        union [
          "binary">:
            doc "A binary literal" binary,
          "boolean">:
            doc "A boolean literal" boolean,
          "float">:
            doc "A floating-point literal" $ core "FloatValue",
          "integer">:
            doc "An integer literal" $
            core "IntegerValue",
          "string">:
            doc "A string literal" string],

      def "LiteralType" $
        doc "Any of a fixed set of literal types, also called atomic types, base types, primitive types, or type constants" $
        union [
          "binary">:
             doc "The type of a binary (byte string) value" unit,
          "boolean">:
            doc "The type of a boolean (true/false) value" unit,
          "float">:
            doc "The type of a floating-point value" $
            core "FloatType",
          "integer">:
            doc "The type of an integer value" $
            core "IntegerType",
          "string">:
            doc "The type of a string value" unit],

      def "MapType" $
        doc "A map type" $
        record [
          "keys">: core "Type",
          "values">: core "Type"],

      def "Name" $
        doc "A unique identifier in some context; a string-valued key"
        $ wrap string,

      def "OptionalCases" $
        doc "A case statement for matching optional terms" $
        record [
          "nothing">:
            doc "A term provided if the optional value is nothing" $
            core "Term",
          "just">:
            doc "A function which is applied if the optional value is non-nothing" $
            core "Term"],

      def "Projection" $
        doc "A record elimination; a projection" $
        record [
          "typeName">:
            doc "The name of the record type" $
            core "Name",
          "field">:
            doc "The name of the projected field" $
            core "Name"],

      def "Record" $
        doc "A record, or labeled tuple; a map of field names to terms" $
        record [
          "typeName">: core "Name",
          "fields">: list $ core "Field"],

      def "RowType" $
        doc "A labeled record or union type" $
        record [
          "typeName">:
            doc "The name of the row type, which must correspond to the name of a Type element" $
            core "Name",
          "fields">:
            doc "The fields of this row type, excluding any inherited fields" $
            list $ core "FieldType"],

      def "Sum" $
        doc "The unlabeled equivalent of an Injection term" $
        record [
          "index">: int32,
          "size">: int32,
          "term">: core "Term"],

      def "Term" $
        doc "A data term" $
        union [
          "annotated">:
            doc "A term annotated with metadata" $
            core "AnnotatedTerm",
          "application">:
            doc "A function application" $
            core "Application",
          "function">:
            doc "A function term" $
            core "Function",
          "let">:
            core "Let",
          "list">:
            doc "A list" $
            list $ core "Term",
          -- TODO: list elimination
          "literal">:
            doc "A literal value" $
            core "Literal",
          "map">:
            doc "A map of keys to values" $
            Types.map (core "Term") (core "Term"),
          "optional">:
            doc "An optional value" $
            optional $ core "Term",
          "product">:
            doc "A tuple" $
            list (core "Term"),
          "record">:
            doc "A record term" $
            core "Record",
          "set">:
            doc "A set of values" $
            set $ core "Term",
          "sum">:
            doc "A variant tuple" $
            core "Sum",
          "typeAbstraction">:
            doc "A System F type abstraction term" $
            core "TypeAbstraction",
          "typeApplication">:
            doc "A System F type application term" $
            core "TypedTerm",
          "typed">:
            doc "A term annotated with its type" $
            core "TypedTerm",
          "union">:
            doc "An injection; an instance of a union type" $
            core "Injection",
          "variable">:
            doc "A variable reference" $
            core "Name",
          "wrap">:
            core "WrappedTerm"],

      def "TupleProjection" $
        doc "A tuple elimination; a projection from an integer-indexed product" $
        record [
          "arity">:
            doc "The arity of the tuple"
            int32,
          "index">:
            doc "The 0-indexed offset from the beginning of the tuple"
            int32],

      def "Type" $
        doc "A data type" $
        union [
          "annotated">: core "AnnotatedType",
          "application">: core "ApplicationType",
          "function">: core "FunctionType",
          "lambda">: core "LambdaType",
          "list">: core "Type",
          "literal">: core "LiteralType",
          "map">: core "MapType",
          "optional">: core "Type",
          "product">: list (core "Type"),
          "record">: core "RowType",
          "set">: core "Type",
          "sum">: list (core "Type"),
          "union">: core "RowType",
          "variable">: core "Name",
          "wrap">: core "WrappedType"],

      def "TypeAbstraction" $
        doc "A System F type abstraction term" $
        record [
          "parameter">:
            doc "The type variable introduced by the abstraction" $
            core "Name",
          "body">:
            doc "The body of the abstraction" $
            core "Term"],

      def "TypeScheme" $
        doc "A type expression together with free type variables occurring in the expression" $
        record [
          "variables">: list $ core "Name",
          "type">: core "Type"],

      def "TypedTerm" $
        doc "A term together with its type" $
        record [
          "term">: core "Term",
          "type">: core "Type"],

      def "Unit" $
        doc "An empty record as a canonical unit value" $
        record [],

      def "WrappedTerm" $
        doc "A term wrapped in a type name" $
        record [
          "typeName">: core "Name",
          "object">: core "Term"],

      def "WrappedType" $
        doc "A type wrapped in a type name" $
        record [
          "typeName">: core "Name",
          "object">: core "Type"]]
