{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Ext.Pg.Graphson.Syntax where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types

import Hydra.Sources.Core


graphsonSyntaxModule :: Module
graphsonSyntaxModule = Module ns elements [] tier0Modules $
    Just ("A syntax model for TinkerPop's GraphSON format."
      ++ " This model is designed to be as inclusive as possible, supporting GraphSON 4.0 as well as earlier versions."
      ++ " See https://github.com/apache/tinkerpop/blob/master/docs/src/dev/io/graphson.asciidoc.")
  where
    ns = Namespace "hydra/pg/graphson/syntax"
    gson = typeref ns
    def = datatype ns

    elements = [

      def "BigDecimalValue" $
        wrap string,

      def "CompositeTypedValue" $
        record [
          "type">: gson "TypeName",
          "fields">: gson "Map"],

      def "DateTime" $
        wrap string,

      def "DoubleValue" $
        union [
          "finite">: float64,
          "infinity">: unit,
          "negativeInfinity">: unit,
          "notANumber">: unit],

      def "Duration" $
        wrap string,

      def "EdgeLabel" $
        wrap string,

      def "FloatValue" $
        union [
          "finite">: float32,
          "infinity">: unit,
          "negativeInfinity">: unit,
          "notANumber">: unit],

      def "Map" $
        list $ gson "ValuePair",

      def "OutEdgeValue" $
        record [
          "id">: gson "Value",
          "inVertexId">: gson "Value",
          "properties">: Types.map (gson "PropertyKey") (gson "Value")],

      def "PrimitiveTypedValue" $
        record [
          "type">: gson "TypeName",
          "value">: string],

      def "PropertyKey" $
        wrap string,

      def "TypeName" $
        wrap string,

      def "Uuid" $
        wrap string,

      -- Note: the following are currently unsupported as values:
      --   * BulkSet
      --   * Direction
      --   * Edge
      --   * Error Result
      --   * Graph
      --   * Path
      --   * Property
      --   * Standard Request
      --   * Standard Result
      --   * T (enum value)
      --   * Tree
      --   * Vertex
      --   * VertexProperty
      def "Value" $
        union [
          "bigDecimal">: gson "BigDecimalValue",
          "bigInteger">: bigint,
          "binary">: binary,
          "boolean">: boolean,
          "byte">: uint8,
          "char">: uint32,
          "composite">: gson "CompositeTypedValue",
          "dateTime">: gson "DateTime",
          "double">: gson "DoubleValue",
          "duration">: gson "Duration",
          "float">: gson "FloatValue",
          "integer">: int32,
          "list">: list $ gson "Value",
          "long">: int64,
          "map">: gson "Map",
          "null">: unit,
          "primitive">: gson "PrimitiveTypedValue",
          "set">: list $ gson "Value",
          "short">: int16,
          "string">: string,
          "uuid">: gson "Uuid"],

      def "ValuePair" $
        record [
          "first">: gson "Value",
          "second">: gson "Value"],

      def "Vertex" $
        record [
          "id">: gson "Value",
          "label">: optional $ gson "VertexLabel",
          "outEdges">: Types.map (gson "EdgeLabel") (nonemptyList $ gson "OutEdgeValue"),
          "properties">: Types.map (gson "PropertyKey") (nonemptyList $ gson "VertexPropertyValue")],

      def "VertexLabel" $
        wrap string,

      def "VertexPropertyValue" $
        record [
          "id">: optional $ gson "Value",
          "value">: gson "Value"]]
