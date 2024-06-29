-- | A model derived from TinkerPop's Graph.Features. See
-- |   https://tinkerpop.apache.org/javadocs/current/core/org/apache/tinkerpop/gremlin/structure/Graph.Features.html
-- | 
-- | An interface that represents the capabilities of a Graph implementation.
-- | By default all methods of features return true and it is up to implementers to disable feature they don't support.
-- | Users should check features prior to using various functions of TinkerPop to help ensure code portability across implementations.
-- | For example, a common usage would be to check if a graph supports transactions prior to calling the commit method on Graph.tx().

module Hydra.Langs.Tinkerpop.Features where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | Base interface for features that relate to supporting different data types.
data DataTypeFeatures = 
  DataTypeFeatures {
    -- | Supports setting of an array of boolean values.
    dataTypeFeaturesSupportsBooleanArrayValues :: Bool,
    -- | Supports setting of a boolean value.
    dataTypeFeaturesSupportsBooleanValues :: Bool,
    -- | Supports setting of an array of byte values.
    dataTypeFeaturesSupportsByteArrayValues :: Bool,
    -- | Supports setting of a byte value.
    dataTypeFeaturesSupportsByteValues :: Bool,
    -- | Supports setting of an array of double values.
    dataTypeFeaturesSupportsDoubleArrayValues :: Bool,
    -- | Supports setting of a double value.
    dataTypeFeaturesSupportsDoubleValues :: Bool,
    -- | Supports setting of an array of float values.
    dataTypeFeaturesSupportsFloatArrayValues :: Bool,
    -- | Supports setting of a float value.
    dataTypeFeaturesSupportsFloatValues :: Bool,
    -- | Supports setting of an array of integer values.
    dataTypeFeaturesSupportsIntegerArrayValues :: Bool,
    -- | Supports setting of a integer value.
    dataTypeFeaturesSupportsIntegerValues :: Bool,
    -- | Supports setting of an array of long values.
    dataTypeFeaturesSupportsLongArrayValues :: Bool,
    -- | Supports setting of a long value.
    dataTypeFeaturesSupportsLongValues :: Bool,
    -- | Supports setting of a Map value.
    dataTypeFeaturesSupportsMapValues :: Bool,
    -- | Supports setting of a List value.
    dataTypeFeaturesSupportsMixedListValues :: Bool,
    -- | Supports setting of a Java serializable value.
    dataTypeFeaturesSupportsSerializableValues :: Bool,
    -- | Supports setting of an array of string values.
    dataTypeFeaturesSupportsStringArrayValues :: Bool,
    -- | Supports setting of a string value.
    dataTypeFeaturesSupportsStringValues :: Bool,
    -- | Supports setting of a List value.
    dataTypeFeaturesSupportsUniformListValues :: Bool}
  deriving (Eq, Ord, Read, Show)

_DataTypeFeatures = (Core.Name "hydra/langs/tinkerpop/features.DataTypeFeatures")

_DataTypeFeatures_supportsBooleanArrayValues = (Core.Name "supportsBooleanArrayValues")

_DataTypeFeatures_supportsBooleanValues = (Core.Name "supportsBooleanValues")

_DataTypeFeatures_supportsByteArrayValues = (Core.Name "supportsByteArrayValues")

_DataTypeFeatures_supportsByteValues = (Core.Name "supportsByteValues")

_DataTypeFeatures_supportsDoubleArrayValues = (Core.Name "supportsDoubleArrayValues")

_DataTypeFeatures_supportsDoubleValues = (Core.Name "supportsDoubleValues")

_DataTypeFeatures_supportsFloatArrayValues = (Core.Name "supportsFloatArrayValues")

_DataTypeFeatures_supportsFloatValues = (Core.Name "supportsFloatValues")

_DataTypeFeatures_supportsIntegerArrayValues = (Core.Name "supportsIntegerArrayValues")

_DataTypeFeatures_supportsIntegerValues = (Core.Name "supportsIntegerValues")

_DataTypeFeatures_supportsLongArrayValues = (Core.Name "supportsLongArrayValues")

_DataTypeFeatures_supportsLongValues = (Core.Name "supportsLongValues")

_DataTypeFeatures_supportsMapValues = (Core.Name "supportsMapValues")

_DataTypeFeatures_supportsMixedListValues = (Core.Name "supportsMixedListValues")

_DataTypeFeatures_supportsSerializableValues = (Core.Name "supportsSerializableValues")

_DataTypeFeatures_supportsStringArrayValues = (Core.Name "supportsStringArrayValues")

_DataTypeFeatures_supportsStringValues = (Core.Name "supportsStringValues")

_DataTypeFeatures_supportsUniformListValues = (Core.Name "supportsUniformListValues")

-- | Features that are related to Edge operations.
data EdgeFeatures = 
  EdgeFeatures {
    edgeFeaturesElementFeatures :: ElementFeatures,
    edgeFeaturesProperties :: EdgePropertyFeatures,
    -- | Determines if an Edge can be added to a Vertex.
    edgeFeaturesSupportsAddEdges :: Bool,
    -- | Determines if an Edge can be removed from a Vertex.
    edgeFeaturesSupportsRemoveEdges :: Bool,
    -- | Determines if the Graph implementation uses upsert functionality as opposed to insert functionality for Vertex.addEdge(String, Vertex, Object...).
    edgeFeaturesSupportsUpsert :: Bool}
  deriving (Eq, Ord, Read, Show)

_EdgeFeatures = (Core.Name "hydra/langs/tinkerpop/features.EdgeFeatures")

_EdgeFeatures_elementFeatures = (Core.Name "elementFeatures")

_EdgeFeatures_properties = (Core.Name "properties")

_EdgeFeatures_supportsAddEdges = (Core.Name "supportsAddEdges")

_EdgeFeatures_supportsRemoveEdges = (Core.Name "supportsRemoveEdges")

_EdgeFeatures_supportsUpsert = (Core.Name "supportsUpsert")

-- | Features that are related to Edge Property objects.
data EdgePropertyFeatures = 
  EdgePropertyFeatures {
    edgePropertyFeaturesPropertyFeatures :: PropertyFeatures}
  deriving (Eq, Ord, Read, Show)

_EdgePropertyFeatures = (Core.Name "hydra/langs/tinkerpop/features.EdgePropertyFeatures")

_EdgePropertyFeatures_propertyFeatures = (Core.Name "propertyFeatures")

-- | Features that are related to Element objects.
data ElementFeatures = 
  ElementFeatures {
    -- | Determines if an Element allows properties to be added.
    elementFeaturesSupportsAddProperty :: Bool,
    -- | Determines if an Element any Java object is a suitable identifier.
    elementFeaturesSupportsAnyIds :: Bool,
    -- | Determines if an Element has a specific custom object as their internal representation.
    elementFeaturesSupportsCustomIds :: Bool,
    -- | Determines if an Element has numeric identifiers as their internal representation.
    elementFeaturesSupportsNumericIds :: Bool,
    -- | Determines if an Element allows properties to be removed.
    elementFeaturesSupportsRemoveProperty :: Bool,
    -- | Determines if an Element has string identifiers as their internal representation.
    elementFeaturesSupportsStringIds :: Bool,
    -- | Determines if an Element can have a user defined identifier.
    elementFeaturesSupportsUserSuppliedIds :: Bool,
    -- | Determines if an Element has UUID identifiers as their internal representation.
    elementFeaturesSupportsUuidIds :: Bool}
  deriving (Eq, Ord, Read, Show)

_ElementFeatures = (Core.Name "hydra/langs/tinkerpop/features.ElementFeatures")

_ElementFeatures_supportsAddProperty = (Core.Name "supportsAddProperty")

_ElementFeatures_supportsAnyIds = (Core.Name "supportsAnyIds")

_ElementFeatures_supportsCustomIds = (Core.Name "supportsCustomIds")

_ElementFeatures_supportsNumericIds = (Core.Name "supportsNumericIds")

_ElementFeatures_supportsRemoveProperty = (Core.Name "supportsRemoveProperty")

_ElementFeatures_supportsStringIds = (Core.Name "supportsStringIds")

_ElementFeatures_supportsUserSuppliedIds = (Core.Name "supportsUserSuppliedIds")

_ElementFeatures_supportsUuidIds = (Core.Name "supportsUuidIds")

-- | Additional features which are needed for the complete specification of language constraints in Hydra, above and beyond TinkerPop Graph.Features
data ExtraFeatures a = 
  ExtraFeatures {
    extraFeaturesSupportsMapKey :: (Core.Type -> Bool)}

_ExtraFeatures = (Core.Name "hydra/langs/tinkerpop/features.ExtraFeatures")

_ExtraFeatures_supportsMapKey = (Core.Name "supportsMapKey")

-- | An interface that represents the capabilities of a Graph implementation. By default all methods of features return true and it is up to implementers to disable feature they don't support. Users should check features prior to using various functions of TinkerPop to help ensure code portability across implementations. For example, a common usage would be to check if a graph supports transactions prior to calling the commit method on Graph.tx().
-- | 
-- | As an additional notice to Graph Providers, feature methods will be used by the test suite to determine which tests will be ignored and which will be executed, therefore proper setting of these features is essential to maximizing the amount of testing performed by the suite. Further note, that these methods may be called by the TinkerPop core code to determine what operations may be appropriately executed which will have impact on features utilized by users.
data Features = 
  Features {
    -- | Gets the features related to edge operation.
    featuresEdge :: EdgeFeatures,
    -- | Gets the features related to graph operation.
    featuresGraph :: GraphFeatures,
    -- | Gets the features related to vertex operation.
    featuresVertex :: VertexFeatures}
  deriving (Eq, Ord, Read, Show)

_Features = (Core.Name "hydra/langs/tinkerpop/features.Features")

_Features_edge = (Core.Name "edge")

_Features_graph = (Core.Name "graph")

_Features_vertex = (Core.Name "vertex")

-- | Features specific to a operations of a graph.
data GraphFeatures = 
  GraphFeatures {
    -- | Determines if the Graph implementation supports GraphComputer based processing.
    graphFeaturesSupportsComputer :: Bool,
    -- | Determines if the Graph implementation supports more than one connection to the same instance at the same time.
    graphFeaturesSupportsConcurrentAccess :: Bool,
    -- | Determines if the Graph implementations supports read operations as executed with the GraphTraversalSource.io(String) step.
    graphFeaturesSupportsIoRead :: Bool,
    -- | Determines if the Graph implementations supports write operations as executed with the GraphTraversalSource.io(String) step.
    graphFeaturesSupportsIoWrite :: Bool,
    -- | Determines if the Graph implementation supports persisting it's contents natively to disk.
    graphFeaturesSupportsPersistence :: Bool,
    -- | Determines if the Graph implementation supports threaded transactions which allow a transaction to be executed across multiple threads via Transaction.createThreadedTx().
    graphFeaturesSupportsThreadedTransactions :: Bool,
    -- | Determines if the Graph implementations supports transactions.
    graphFeaturesSupportsTransactions :: Bool,
    -- | Gets the features related to graph sideEffects operation.
    graphFeaturesVariables :: VariableFeatures}
  deriving (Eq, Ord, Read, Show)

_GraphFeatures = (Core.Name "hydra/langs/tinkerpop/features.GraphFeatures")

_GraphFeatures_supportsComputer = (Core.Name "supportsComputer")

_GraphFeatures_supportsConcurrentAccess = (Core.Name "supportsConcurrentAccess")

_GraphFeatures_supportsIoRead = (Core.Name "supportsIoRead")

_GraphFeatures_supportsIoWrite = (Core.Name "supportsIoWrite")

_GraphFeatures_supportsPersistence = (Core.Name "supportsPersistence")

_GraphFeatures_supportsThreadedTransactions = (Core.Name "supportsThreadedTransactions")

_GraphFeatures_supportsTransactions = (Core.Name "supportsTransactions")

_GraphFeatures_variables = (Core.Name "variables")

-- | A base interface for Edge or Vertex Property features.
data PropertyFeatures = 
  PropertyFeatures {
    propertyFeaturesDataTypeFeatures :: DataTypeFeatures,
    -- | Determines if an Element allows for the processing of at least one data type defined by the features.
    propertyFeaturesSupportsProperties :: Bool}
  deriving (Eq, Ord, Read, Show)

_PropertyFeatures = (Core.Name "hydra/langs/tinkerpop/features.PropertyFeatures")

_PropertyFeatures_dataTypeFeatures = (Core.Name "dataTypeFeatures")

_PropertyFeatures_supportsProperties = (Core.Name "supportsProperties")

-- | Features for Graph.Variables.
data VariableFeatures = 
  VariableFeatures {
    variableFeaturesDataTypeFeatures :: DataTypeFeatures,
    -- | If any of the features on Graph.Features.VariableFeatures is true then this value must be true.
    variableFeaturesSupportsVariables :: Bool}
  deriving (Eq, Ord, Read, Show)

_VariableFeatures = (Core.Name "hydra/langs/tinkerpop/features.VariableFeatures")

_VariableFeatures_dataTypeFeatures = (Core.Name "dataTypeFeatures")

_VariableFeatures_supportsVariables = (Core.Name "supportsVariables")

-- | Features that are related to Vertex operations.
data VertexFeatures = 
  VertexFeatures {
    vertexFeaturesElementFeatures :: ElementFeatures,
    vertexFeaturesProperties :: VertexPropertyFeatures,
    -- | Determines if a Vertex can be added to the Graph.
    vertexFeaturesSupportsAddVertices :: Bool,
    -- | Determines if a Vertex can support non-unique values on the same key.
    vertexFeaturesSupportsDuplicateMultiProperties :: Bool,
    -- | Determines if a Vertex can support properties on vertex properties.
    vertexFeaturesSupportsMetaProperties :: Bool,
    -- | Determines if a Vertex can support multiple properties with the same key.
    vertexFeaturesSupportsMultiProperties :: Bool,
    -- | Determines if a Vertex can be removed from the Graph.
    vertexFeaturesSupportsRemoveVertices :: Bool,
    -- | Determines if the Graph implementation uses upsert functionality as opposed to insert functionality for Graph.addVertex(String).
    vertexFeaturesSupportsUpsert :: Bool}
  deriving (Eq, Ord, Read, Show)

_VertexFeatures = (Core.Name "hydra/langs/tinkerpop/features.VertexFeatures")

_VertexFeatures_elementFeatures = (Core.Name "elementFeatures")

_VertexFeatures_properties = (Core.Name "properties")

_VertexFeatures_supportsAddVertices = (Core.Name "supportsAddVertices")

_VertexFeatures_supportsDuplicateMultiProperties = (Core.Name "supportsDuplicateMultiProperties")

_VertexFeatures_supportsMetaProperties = (Core.Name "supportsMetaProperties")

_VertexFeatures_supportsMultiProperties = (Core.Name "supportsMultiProperties")

_VertexFeatures_supportsRemoveVertices = (Core.Name "supportsRemoveVertices")

_VertexFeatures_supportsUpsert = (Core.Name "supportsUpsert")

-- | Features that are related to Vertex Property objects.
data VertexPropertyFeatures = 
  VertexPropertyFeatures {
    vertexPropertyFeaturesDataTypeFeatures :: DataTypeFeatures,
    vertexPropertyFeaturesPropertyFeatures :: PropertyFeatures,
    vertexPropertyFeaturesElementFeatures :: ElementFeatures,
    -- | Determines if a VertexProperty allows properties to be removed.
    vertexPropertyFeaturesSupportsRemove :: Bool}
  deriving (Eq, Ord, Read, Show)

_VertexPropertyFeatures = (Core.Name "hydra/langs/tinkerpop/features.VertexPropertyFeatures")

_VertexPropertyFeatures_dataTypeFeatures = (Core.Name "dataTypeFeatures")

_VertexPropertyFeatures_propertyFeatures = (Core.Name "propertyFeatures")

_VertexPropertyFeatures_elementFeatures = (Core.Name "elementFeatures")

_VertexPropertyFeatures_supportsRemove = (Core.Name "supportsRemove")
