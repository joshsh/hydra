{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Ext.TypeScript.Model where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types


typeScriptNs = Namespace "hydra/ext/typeScript/model"
ts = typeref typeScriptNs

typeScriptModelModule :: Module
typeScriptModelModule = Module typeScriptNs elements [hydraCoreModule] [hydraCoreModule] $
    Just ("A basic TypeScript model, constructed on the basis of the typescriptlang.org documentation")
  where
    def = datatype typeScriptNs
    elements = [

      def "FunctionType" $
        record [
          "parameters">: list $ ts "Parameter",
          "range">: ts "Type"],

      def "Parameter" $
        record [
          "name">: string,
          "type">: ts "Type"],

      def "PrimitiveType" $
        union [
          "bigint">:
            doc "integers in the arbitrary precision format"
            unit,
          "boolean">:
            doc "true and false"
            unit,
          "null">:
            doc "equivalent to the unit type"
            unit,
          "number">:
            doc "a double-precision IEEE 754 floating point"
            unit,
          "object">:
            doc "similar to records"
            unit,
          "string">:
            doc "an immutable UTF-16 string"
            unit,
          "symbol">:
            doc "a unique value usually used as a key"
            unit,
          "undefined">:
            doc "also equivalent to the unit type"
            unit],

      def "Type" $
        union [
          "array">:
            doc "mutable arrays, also written Array<T>" $
            ts "Type",
          "function">:
            doc "functions" $
            ts "FunctionType",
          "never">:
            doc "the bottom type"
            unit,
          "objectLiteral">:
            doc "e.g. { property: Type }"
            unit,
          "primitive">:
            doc "A primitive type" $
            ts "PrimitiveType",
          "tuple">:
            doc "tuples, which are fixed-length but mutable" $
            list $ ts "Type",
          "unknown">:
            doc "The top type"
            unit,
          "void">:
            doc "for functions with no documented return value"
            unit]
        ]
