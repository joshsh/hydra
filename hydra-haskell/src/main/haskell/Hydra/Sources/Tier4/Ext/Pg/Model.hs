{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Ext.Pg.Model where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types

import Hydra.Sources.Core


pgModelModule :: Module
pgModelModule = Module ns elements [] tier0Modules $
    Just ("A typed property graph data model. " ++
      "Property graphs are parameterized a type for property and id values, " ++
      "while property graph schemas are parameterized by a type for property and id types")
  where
    ns = Namespace "hydra/pg/model"
    pg = typeref ns
    def = datatype ns

    elements = [

      def "Direction" $
        doc "The direction of an edge or edge pattern" $
          enum ["out", "in", "both", "undirected"],

      def "Edge" $
        doc "An edge" $
        lambda "v" $ record [
          "label">:
            doc "The label of the edge" $
            pg "EdgeLabel",
          "id">:
            doc "The unique identifier of the edge"
            "v",
          "out">:
            doc "The id of the out-vertex (tail) of the edge"
            "v",
          "in">:
            doc "The id of the in-vertex (head) of the edge"
            "v",
          "properties">:
            doc "A key/value map of edge properties" $
            Types.map (pg "PropertyKey") "v"],

      def "EdgeLabel" $
        doc "The label of an edge" $
        string,

      def "EdgeType" $
        doc "The type of an edge" $
        lambda "t" $ record [
            "label">:
              doc "The label of any edge of this edge type" $
              pg "EdgeLabel",
            "id">:
              doc "The type of the id of any edge of this edge type"
              "t",
            "out">:
              doc "The label of the out-vertex (tail) of any edge of this edge type" $
              pg "VertexLabel",
            "in">:
              doc "The label of the in-vertex (head) of any edge of this edge type" $
              pg "VertexLabel",
            "properties">:
              doc "A list of property types. The types are ordered for the sake of applications in which property order is significant." $
              list (pg "PropertyType" @@ "t")],

      def "Element" $
        doc "Either a vertex or an edge" $
        lambda "v" $ union [
          "vertex">: pg "Vertex" @@ "v",
          "edge">: pg "Edge" @@ "v"],

      def "ElementKind" $
        doc "The kind of an element: vertex or edge" $
        enum ["vertex", "edge"],

      def "ElementTree" $
        doc "An element together with its dependencies in some context" $
        lambda "v" $ record [
          "self">: pg "Element" @@ "v",
          "dependencies">: Types.list $ pg "ElementTree" @@ "v"],

      def "ElementType" $
        doc "The type of a vertex or edge" $
        lambda "t" $ union [
          "vertex">: pg "VertexType" @@ "t",
          "edge">: pg "EdgeType" @@ "t"],

      def "ElementTypeTree" $
        doc "An element type together with its dependencies in some context" $
        lambda "t" $ record [
          "self">: pg "ElementType" @@ "t",
          "dependencies">: Types.list $ pg "ElementTypeTree" @@ "t"],

      def "Graph" $
        doc "A graph; a self-contained collection of vertices and edges" $
        lambda "v" $ record [
          "vertices">: Types.map "v" $ pg "Vertex" @@ "v",
          "edges">: Types.map "v" $ pg "Edge" @@ "v"],

      def "GraphSchema" $
        doc "A graph schema; a vertex and edge types for the vertices and edges of a graph conforming to the schema" $
        lambda "t" $ record [
          "vertices">:
            doc "A unique vertex type for each vertex label which may occur in a graph" $
            Types.map (pg "VertexLabel") (pg "VertexType" @@ "t"),
          "edges">:
            doc "A unique edge type for each edge label which may occur in a graph" $
            Types.map (pg "EdgeLabel") (pg "EdgeType" @@ "t")],

      def "Label" $
        doc "Either a vertex or edge label" $
        union [
          "vertex">: pg "VertexLabel",
          "edge">: pg "EdgeLabel"],

      def "Property" $
        doc "A key/value property" $
        lambda "v" $ record [
          "key">:
            doc "They key of the property" $
            pg "PropertyKey",
          "value">:
            doc "The value of the property"
            "v"],

      def "PropertyKey" $
        doc "A property key"
        string,

      def "PropertyType" $
        doc "The type of a property" $
        lambda "t" $ record [
          "key">:
            doc "A property's key" $
            pg "PropertyKey",
          "value">:
            doc "The type of a property's value"
            "t",
          "required">:
            doc "Whether the property is required; values may be omitted from a property map otherwise"
            boolean],

      def "Vertex" $
        doc "A vertex" $
        lambda "v" $ record [
          "label">:
            doc "The label of the vertex" $
            pg "VertexLabel",
          "id">:
            doc "The unique identifier of the vertex"
            "v",
          "properties">:
            doc "A key/value map of vertex properties" $
            Types.map (pg "PropertyKey") "v"],

      def "VertexLabel" $
        doc "The label of a vertex. The default (null) vertex is represented by the empty string" $
        string,

      def "VertexType" $
        doc "The type of a vertex" $
        lambda "t" $ record [
          "label">:
            doc "The label of any vertex of this vertex type" $
            pg "VertexLabel",
          "id">:
            doc "The type of the id of any vertex of this vertex type"
            "t",
          "properties">:
            doc "A list of property types. The types are ordered for the sake of applications in which property order is significant." $
            list (pg "PropertyType" @@ "t")],

      def "VertexWithAdjacentEdges" $
        doc "A vertex together with any outgoing and/or incoming edges; a vertex object" $
        lambda "v" $ record [
          "vertex">:
            doc "The focus vertex" $
            pg "Vertex" @@ "v",
          "inEdges">:
            doc "An adjacency list of edges in which the focus vertex is the head (in-vertex) of the edge" $
            list (pg "Edge" @@ "v"),
          "outEdges">:
            doc "An adjacency list of edges in which the focus vertex is the tail (out-vertex) of the edge" $
            list (pg "Edge" @@ "v")]]
