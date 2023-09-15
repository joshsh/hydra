{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Core(
  hydraCore,
  hydraCoreModule,
  module Hydra.Kernel,
) where

import Hydra.Kernel
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types


hydraCore :: Graph Kv
hydraCore = elementsToGraph bootstrapGraph Nothing (moduleElements hydraCoreModule)

hydraCoreModule :: Module Kv
hydraCoreModule = Module ns elements [] $
    Just "Hydra's core data model, defining types, terms, and their dependencies"
  where
    ns = Namespace "hydra/core"
    core = typeref ns
    def = datatype ns
    doc s = setTypeDescription (Just s)

    elements = [

      def "Annotated" $
        doc "An object, such as a type or term, together with an annotation" $
        lambda "x" $ lambda "a" $ record [
          "subject">: "x",
          "annotation">: "a"],

      def "Application" $
        doc "A term which applies a function to an argument" $
        lambda "a" $ record [
          "function">:
            doc "The left-hand side of the application" $
            core "Term" @@ "a",
          "argument">:
            doc "The right-hand side of the application" $
            core "Term" @@ "a"],

      def "ApplicationType" $
        doc "The type-level analog of an application term" $
        lambda "a" $ record [
          "function">:
            doc "The left-hand side of the application" $
            core "Type" @@ "a",
          "argument">:
            doc "The right-hand side of the application" $
            core "Type" @@ "a"],

      def "CaseStatement" $
        doc "A union elimination; a case statement" $
        lambda "a" $ record [
          "typeName">: core "Name",
          "default">: optional (core "Term" @@ "a"),
          "cases">: list $ core "Field" @@ "a"],

      def "Elimination" $
        doc "A corresponding elimination for an introduction term" $
        lambda "a" $ union [
          "list">:
            doc "Eliminates a list using a fold function; this function has the signature b -> [a] -> b" $
            core "Term" @@ "a",
          "optional">:
            doc "Eliminates an optional term by matching over the two possible cases" $
            core "OptionalCases" @@ "a",
          "product">:
            doc "Eliminates a tuple by projecting the component at a given 0-indexed offset" $
            core "TupleProjection",
          "record">:
            doc "Eliminates a record by projecting a given field" $
            core "Projection",
          "union">:
            doc "Eliminates a union term by matching over the fields of the union. This is a case statement." $
            core "CaseStatement" @@ "a",
          "wrap">:
            doc "Unwrap a wrapped term" $
            core "Name"],

      def "Field" $
        doc "A labeled term" $
        lambda "a" $ record [
          "name">: core "FieldName",
          "term">: core "Term" @@ "a"],

      def "FieldName" $
        doc "The name of a field, unique within a record or union type"
        $ wrap string,

      def "FieldType" $
        doc "The name and type of a field" $
        lambda "a" $ record [
          "name">: core "FieldName",
          "type">: core "Type" @@ "a"],

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
        lambda "a" $ union [
          "elimination">:
            doc "An elimination for any of a few term variants" $
            core "Elimination" @@ "a",
          "lambda">:
            doc "A function abstraction (lambda)" $
            core "Lambda" @@ "a",
          "primitive">:
            doc "A reference to a built-in (primitive) function" $
            core "Name"],

      def "FunctionType" $
        doc "A function type, also known as an arrow type" $
        lambda "a" $ record [
          "domain">: core "Type" @@ "a",
          "codomain">: core "Type" @@ "a"],

      def "Injection" $
        doc "An instance of a union type; i.e. a string-indexed generalization of inl() or inr()" $
        lambda "a" $ record [
          "typeName">: core "Name",
          "field">: core "Field" @@ "a"],

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

      def "Kv" $
        doc "A key/value map which serves as a built-in metadata container for terms" $
        record [
          "annotations">:
            doc "A map of annotation names to annotation values" $
            Types.map string (core "Term" @@ core "Kv")],

      def "Lambda" $
        doc "A function abstraction (lambda)" $
        lambda "a" $ record [
          "parameter">:
            doc "The parameter of the lambda" $
            core "Name",
          "body">:
            doc "The body of the lambda" $
            core "Term" @@ "a"],

      def "LambdaType" $
        doc "A type abstraction; the type-level analog of a lambda term" $
        lambda "a" $ record [
          "parameter">:
            doc "The variable which is bound by the lambda" $
            core "Name",
          "body">:
            doc "The body of the lambda" $
            core "Type" @@ "a"],

      def "Let" $
        doc "A set of (possibly recursive) 'let' bindings" $
        lambda "a" $ record [
          "bindings">: Types.map (core "Name") (core "Term" @@ "a"),
          "environment">: core "Term" @@ "a"],

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
          "binary">: unit,
          "boolean">: unit,
          "float">: core "FloatType",
          "integer">: core "IntegerType",
          "string">: unit],

      def "MapType" $
        doc "A map type" $
        lambda "a" $ record [
          "keys">: core "Type" @@ "a",
          "values">: core "Type" @@ "a"],

      def "Name" $
        doc "A symbol which stands for a term, type, or element"
        $ wrap string,

      def "Nominal" $
        doc "An object wrapped in a type name" $
        lambda "x" $ record [
          "typeName">: core "Name",
          "object">: "x"],

      def "OptionalCases" $
        doc "A case statement for matching optional terms" $
        lambda "a" $ record [
          "nothing">:
            doc "A term provided if the optional value is nothing" $
            core "Term" @@ "a",
          "just">:
            doc "A function which is applied if the optional value is non-nothing" $
            core "Term" @@ "a"],

      def "Projection" $
        doc "A record elimination; a projection" $
        record [
          "typeName">: core "Name",
          "field">: core "FieldName"],

      def "Record" $
        doc "A record, or labeled tuple; a map of field names to terms" $
        lambda "a" $ record [
          "typeName">: core "Name",
          "fields">: list $ core "Field" @@ "a"],

      def "RowType" $
        doc "A labeled record or union type" $
        lambda "a" $ record [
          "typeName">:
            doc "The name of the row type, which must correspond to the name of a Type element" $
            core "Name",
          "extends">:
            doc ("Optionally, the name of another row type which this one extends. If/when field order " ++
                 "is preserved, the inherited fields of the extended type precede those of the extension.") $
            optional $ core "Name",
          "fields">:
            doc "The fields of this row type, excluding any inherited fields" $
            list $ core "FieldType" @@ "a"],

      def "Stream" $
        doc "An infinite stream of terms" $
        lambda "a" $ record [
          "first">: core "Term" @@ "a",
          "rest">: core "Stream" @@ "a"],

      def "Sum" $
        doc "The unlabeled equivalent of an Injection term" $
        lambda "a" $ record [
          "index">: int32,
          "size">: int32,
          "term">: core "Term" @@ "a"],

      def "Term" $
        doc "A data term" $
        lambda "a" $ union [
          "annotated">:
            doc "A term annotated with metadata" $
            core "Annotated" @@ (core "Term" @@ "a") @@ "a",
          "application">:
            doc "A function application" $
            core "Application" @@ "a",
          "function">:
            doc "A function term" $
            core "Function" @@ "a",
          "let">:
            core "Let" @@ "a",
          "list">:
            doc "A list" $
            list $ core "Term" @@ "a",
          -- TODO: list elimination
          "literal">:
            doc "A literal value" $
            core "Literal",
          "map">:
            doc "A map of keys to values" $
            Types.map (core "Term" @@ "a") (core "Term" @@ "a"),
          "optional">:
            doc "An optional value" $
            optional $ core "Term" @@ "a",
          "product">:
            doc "A tuple" $
            list (core "Term" @@ "a"),
          "record">:
            doc "A record term" $
            core "Record" @@ "a",
          "set">:
            doc "A set of values" $
            set $ core "Term" @@ "a",
          "stream">:
            doc "An infinite stream of terms" $
            core "Stream" @@ "a",
          "sum">:
            doc "A variant tuple" $
            core "Sum" @@ "a",
          "union">:
            doc "An injection; an instance of a union type" $
            core "Injection" @@ "a",
          "variable">:
            doc "A variable reference" $
            core "Name",
          "wrap">:
            core "Nominal" @@ (core "Term" @@ "a")],

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
        lambda "a" $ union [
          "annotated">:
            doc "A type annotated with metadata" $
            core "Annotated" @@ (core "Type" @@ "a") @@ "a",
          "application">: core "ApplicationType" @@ "a",
          "function">: core "FunctionType" @@ "a",
          "lambda">: core "LambdaType" @@ "a",
          "list">: core "Type" @@ "a",
          "literal">: core "LiteralType",
          "map">: core "MapType" @@ "a",
          "optional">: core "Type" @@ "a",
          "product">: list (core "Type" @@ "a"),
          "record">: core "RowType" @@ "a",
          "set">: core "Type" @@ "a",
          "stream">: core "Type" @@ "a",
          "sum">: list (core "Type" @@ "a"),
          "union">: core "RowType" @@ "a",
          "variable">: core "Name",
          "wrap">: core "Nominal" @@ (core "Type" @@ "a")],

      def "UnitType" $
        doc "An empty record type as a canonical unit type" $
        record []]
