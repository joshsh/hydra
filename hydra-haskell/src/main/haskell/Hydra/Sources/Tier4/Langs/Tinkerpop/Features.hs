{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Langs.Tinkerpop.Features where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types


tinkerpopFeaturesModule :: Module
tinkerpopFeaturesModule = Module ns elements [hydraCoreModule] $
    Just ("A model derived from TinkerPop's Graph.Features. See\n" ++
      "  https://tinkerpop.apache.org/javadocs/current/core/org/apache/tinkerpop/gremlin/structure/Graph.Features.html\n" ++
      "\n" ++
      "An interface that represents the capabilities of a Graph implementation.\n" ++
      "By default all methods of features return true and it is up to implementers to disable feature they don't support.\n" ++
      "Users should check features prior to using various functions of TinkerPop to help ensure code portability across implementations.\n" ++
      "For example, a common usage would be to check if a graph supports transactions prior to calling the commit method on Graph.tx().")
  where
    ns = Namespace "hydra/langs/tinkerpop/features"
    core = typeref $ moduleNamespace hydraCoreModule
    features = typeref ns
    def = datatype ns
    supports name comment = ("supports" ++ capitalize name)>: doc comment boolean

    elements = [

      def "DataTypeFeatures" $
        doc "Base interface for features that relate to supporting different data types." $
        record [
          supports "booleanArrayValues" "Supports setting of an array of boolean values.",
          supports "booleanValues" "Supports setting of a boolean value.",
          supports "byteArrayValues" "Supports setting of an array of byte values.",
          supports "byteValues" "Supports setting of a byte value.",
          supports "doubleArrayValues" "Supports setting of an array of double values.",
          supports "doubleValues" "Supports setting of a double value.",
          supports "floatArrayValues" "Supports setting of an array of float values.",
          supports "floatValues" "Supports setting of a float value.",
          supports "integerArrayValues" "Supports setting of an array of integer values.",
          supports "integerValues" "Supports setting of a integer value.",
          supports "longArrayValues" "Supports setting of an array of long values.",
          supports "longValues" "Supports setting of a long value.",
          supports "mapValues" "Supports setting of a Map value.",
          supports "mixedListValues" "Supports setting of a List value.",
          supports "serializableValues" "Supports setting of a Java serializable value.",
          supports "stringArrayValues" "Supports setting of an array of string values.",
          supports "stringValues" "Supports setting of a string value.",
          supports "uniformListValues" "Supports setting of a List value."],

      def "EdgeFeatures" $
        doc "Features that are related to Edge operations." $
        record [
          "elementFeatures">: features "ElementFeatures",
          "properties">: features "EdgePropertyFeatures",
          supports "addEdges" "Determines if an Edge can be added to a Vertex.",
          supports "removeEdges" "Determines if an Edge can be removed from a Vertex.",
          supports "upsert" ("Determines if the Graph implementation uses upsert functionality as opposed to insert " ++
            "functionality for Vertex.addEdge(String, Vertex, Object...).")],

      def "EdgePropertyFeatures" $
        doc "Features that are related to Edge Property objects." $
        record [
          "propertyFeatures">: features "PropertyFeatures"],

      def "ElementFeatures" $
        doc "Features that are related to Element objects." $
        record [
          supports "addProperty" "Determines if an Element allows properties to be added.",
          supports "anyIds" "Determines if an Element any Java object is a suitable identifier.",
          supports "customIds" "Determines if an Element has a specific custom object as their internal representation.",
          supports "numericIds" "Determines if an Element has numeric identifiers as their internal representation.",
          supports "removeProperty" "Determines if an Element allows properties to be removed.",
          supports "stringIds" "Determines if an Element has string identifiers as their internal representation.",
          supports "userSuppliedIds" "Determines if an Element can have a user defined identifier.",
          supports "uuidIds" "Determines if an Element has UUID identifiers as their internal representation."
--          , "willAllowId" $
--              doc "Determines if an identifier will be accepted by the Graph." $
--            function (v3 "Id") boolean
            ],

      def "ExtraFeatures" $
        doc ("Additional features which are needed for the complete specification of language constraints in Hydra, "
          ++ "above and beyond TinkerPop Graph.Features") $
        lambda "a" $ record [
          "supportsMapKey">: function (core "Type" @@ "a") boolean],

      def "Features" $
        doc ("An interface that represents the capabilities of a Graph implementation. By default all methods of " ++
            "features return true and it is up to implementers to disable feature they don't support. Users should " ++
            "check features prior to using various functions of TinkerPop to help ensure code portability across " ++
            "implementations. For example, a common usage would be to check if a graph supports transactions prior " ++
            "to calling the commit method on Graph.tx().\n\n" ++
            "As an additional notice to Graph Providers, feature methods will be used by the test suite to " ++
            "determine which tests will be ignored and which will be executed, therefore proper setting of these " ++
            "features is essential to maximizing the amount of testing performed by the suite. Further note, that " ++
            "these methods may be called by the TinkerPop core code to determine what operations may be " ++
            "appropriately executed which will have impact on features utilized by users.") $
        record [
          "edge">: doc "Gets the features related to edge operation." $
            features "EdgeFeatures",
          "graph">: doc "Gets the features related to graph operation." $
            features "GraphFeatures",
          "vertex">: doc "Gets the features related to vertex operation." $
            features "VertexFeatures"],

      def "GraphFeatures" $
        doc "Features specific to a operations of a graph." $
        record [
          supports "computer" "Determines if the Graph implementation supports GraphComputer based processing.",
          supports "concurrentAccess" "Determines if the Graph implementation supports more than one connection to the same instance at the same time.",
          supports "ioRead" "Determines if the Graph implementations supports read operations as executed with the GraphTraversalSource.io(String) step.",
          supports "ioWrite" "Determines if the Graph implementations supports write operations as executed with the GraphTraversalSource.io(String) step.",
          supports "persistence" "Determines if the Graph implementation supports persisting it's contents natively to disk.",
          supports "threadedTransactions" "Determines if the Graph implementation supports threaded transactions which allow a transaction to be executed across multiple threads via Transaction.createThreadedTx().",
          supports "transactions" "Determines if the Graph implementations supports transactions.",
          "variables">:
            doc "Gets the features related to graph sideEffects operation." $
            features "VariableFeatures"
        ],

      def "PropertyFeatures" $
        doc "A base interface for Edge or Vertex Property features." $
        record [
          "dataTypeFeatures">: features "DataTypeFeatures",
          supports "properties" "Determines if an Element allows for the processing of at least one data type defined by the features."],

      def "VariableFeatures" $
        doc "Features for Graph.Variables." $
        record [
          "dataTypeFeatures">: features "DataTypeFeatures",
          supports "variables" "If any of the features on Graph.Features.VariableFeatures is true then this value must be true."],

      def "VertexFeatures" $
        doc "Features that are related to Vertex operations." $
        record [
          "elementFeatures">: features "ElementFeatures",
--          "getCardinality" $ function (v3 "PropertyKey") (v3 "VertexProperty.Cardinality"),
          "properties">: features "VertexPropertyFeatures",
          supports "addVertices" "Determines if a Vertex can be added to the Graph.",
          supports "duplicateMultiProperties" "Determines if a Vertex can support non-unique values on the same key.",
          supports "metaProperties" "Determines if a Vertex can support properties on vertex properties.",
          supports "multiProperties" "Determines if a Vertex can support multiple properties with the same key.",
          supports "removeVertices" "Determines if a Vertex can be removed from the Graph.",
          supports "upsert" ("Determines if the Graph implementation uses upsert functionality as opposed to insert " ++
            "functionality for Graph.addVertex(String).")],

      def "VertexPropertyFeatures" $
        doc "Features that are related to Vertex Property objects." $
        record [
          "dataTypeFeatures">: features "DataTypeFeatures",
          "propertyFeatures">: features "PropertyFeatures",
          -- Note: re-using ElementFeatures here rather than repeating the individual features (which are identical)
          "elementFeatures">: features "ElementFeatures",
          supports "remove" "Determines if a VertexProperty allows properties to be removed."]

--          , def "VertexProperty.Cardinality" $
--            enum ["list", "set", "single"]
      ]
