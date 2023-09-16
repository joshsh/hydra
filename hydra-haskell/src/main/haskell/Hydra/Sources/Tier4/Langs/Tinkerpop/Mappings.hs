{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Langs.Tinkerpop.Mappings where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Langs.Tinkerpop.Mappings
import qualified Hydra.Dsl.Terms as Terms
import Hydra.Dsl.Types as Types
import Hydra.Sources.Tier4.Langs.Tinkerpop.PropertyGraph


tinkerpopMappingsModule :: Module
tinkerpopMappingsModule = Module ns elements [tinkerpopPropertyGraphModule, hydraCoreModule, hydraComputeModule] $
    Just "A model for property graph mapping specifications. See https://github.com/CategoricalData/hydra/wiki/Property-graphs"
  where
    ns = Namespace "hydra/langs/tinkerpop/mappings"
    mappings = typeref ns
    compute = typeref $ moduleNamespace hydraComputeModule
    core = typeref $ moduleNamespace hydraCoreModule
    v3 = typeref $ moduleNamespace tinkerpopPropertyGraphModule
    def = datatype ns
    toField (k, v) = Field k $ Terms.string v

    elements = [

      def "AnnotationSchema" $
        doc "Configurable annotation keys for property graph mapping specifications" $
        record [
          "vertexLabel">: string,
          "edgeLabel">: string,
          "vertexId">: string,
          "edgeId">: string,
          "propertyKey">: string,
          "propertyValue">: string,
          "outVertex">: string,
          "outVertexLabel">: string,
          "inVertex">: string,
          "inVertexLabel">: string,
          "outEdge">: string,
          "outEdgeLabel">: string,
          "inEdge">: string,
          "inEdgeLabel">: string,
          "ignore">: string],

      def "EdgeSpec" $
        doc "A mapping specification producing edges of a specified label." $
        record [
          "label">:
            doc "The label of the target edges, which must conform to the edge type associated with that label." $
            v3 "EdgeLabel",
          "id">:
            doc "A specification of the id of each target edge" $
            mappings "ValueSpec",
          "out">:
            doc "A specification of the out-vertex reference of each target edge" $
            mappings "ValueSpec",
          "in">:
            doc "A specification of the in-vertex reference of each target edge" $
            mappings "ValueSpec",
          "properties">:
            doc "Zero or more property specifications for each target edge" $
            list $ mappings "PropertySpec"],

      def "ElementSpec" $
        doc "Either a vertex specification or an edge specification" $
        union [
          "vertex">: mappings "VertexSpec",
          "edge">: mappings "EdgeSpec"],

      def "PropertySpec" $
        doc "A mapping specification producing properties of a specified key, and values of the appropriate type." $
        record [
          "key">:
            doc "The key of the target properties" $
            v3 "PropertyKey",
          "value">:
            doc "A specification of the value of each target property, which must conform to the type associated with the property key" $
            mappings "ValueSpec"],

      def "Schema" $
        doc "A set of mappings which translates between Hydra terms and annotations, and application-specific property graph types" $
        lambdas ["s", "t", "v"] $
          record [
            "vertexIdTypes">: compute "Coder" @@ "s" @@ "s" @@ (core "Type" @@ "a") @@ "t",
            "vertexIds">: compute "Coder" @@ "s" @@ "s" @@ (core "Term" @@ "a") @@ "v",
            "edgeIdTypes">: compute "Coder" @@ "s" @@ "s" @@ (core "Type" @@ "a") @@ "t",
            "edgeIds">: compute "Coder" @@ "s" @@ "s" @@ (core "Term" @@ "a") @@ "v",
            "propertyTypes">: compute "Coder" @@ "s" @@ "s" @@ (core "Type" @@ "a") @@ "t",
            "propertyValues">: compute "Coder" @@ "s" @@ "s" @@ (core "Term" @@ "a") @@ "v",
            "annotations">: mappings "AnnotationSchema",
            "defaultVertexId">: "v",
            "defaultEdgeId">: "v"],

      def "ValueSpec" $
        doc "A mapping specification producing values (usually literal values) whose type is understood in context" $
        union [
          "value">:
            doc "A trivial no-op specification which passes the entire value"
            unit,
          "pattern">:
            doc "A compact path representing the function, e.g. engine-${engineInfo/model/name}"
            string],

      def "VertexSpec" $
        doc "A mapping specification producing vertices of a specified label" $
        record [
          "label">:
            doc "The label of the target vertices, which must conform to the vertex type associated with that label." $
            v3 "VertexLabel",
          "id">:
            doc "A specification of the id of each target vertex" $
            mappings "ValueSpec",
          "properties">:
            doc "Zero or more property specifications for each target vertex" $
            list $ mappings "PropertySpec"]]
