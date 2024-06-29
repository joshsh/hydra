-- | A model for property graph mapping specifications. See https://github.com/CategoricalData/hydra/wiki/Property-graphs

module Hydra.Langs.Tinkerpop.Mappings where

import qualified Hydra.Compute as Compute
import qualified Hydra.Core as Core
import qualified Hydra.Langs.Tinkerpop.PropertyGraph as PropertyGraph
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | Configurable annotation keys for property graph mapping specifications
data AnnotationSchema = 
  AnnotationSchema {
    annotationSchemaVertexLabel :: String,
    annotationSchemaEdgeLabel :: String,
    annotationSchemaVertexId :: String,
    annotationSchemaEdgeId :: String,
    annotationSchemaPropertyKey :: String,
    annotationSchemaPropertyValue :: String,
    annotationSchemaOutVertex :: String,
    annotationSchemaOutVertexLabel :: String,
    annotationSchemaInVertex :: String,
    annotationSchemaInVertexLabel :: String,
    annotationSchemaOutEdge :: String,
    annotationSchemaOutEdgeLabel :: String,
    annotationSchemaInEdge :: String,
    annotationSchemaInEdgeLabel :: String,
    annotationSchemaIgnore :: String}
  deriving (Eq, Ord, Read, Show)

_AnnotationSchema = (Core.Name "hydra/langs/tinkerpop/mappings.AnnotationSchema")

_AnnotationSchema_vertexLabel = (Core.Name "vertexLabel")

_AnnotationSchema_edgeLabel = (Core.Name "edgeLabel")

_AnnotationSchema_vertexId = (Core.Name "vertexId")

_AnnotationSchema_edgeId = (Core.Name "edgeId")

_AnnotationSchema_propertyKey = (Core.Name "propertyKey")

_AnnotationSchema_propertyValue = (Core.Name "propertyValue")

_AnnotationSchema_outVertex = (Core.Name "outVertex")

_AnnotationSchema_outVertexLabel = (Core.Name "outVertexLabel")

_AnnotationSchema_inVertex = (Core.Name "inVertex")

_AnnotationSchema_inVertexLabel = (Core.Name "inVertexLabel")

_AnnotationSchema_outEdge = (Core.Name "outEdge")

_AnnotationSchema_outEdgeLabel = (Core.Name "outEdgeLabel")

_AnnotationSchema_inEdge = (Core.Name "inEdge")

_AnnotationSchema_inEdgeLabel = (Core.Name "inEdgeLabel")

_AnnotationSchema_ignore = (Core.Name "ignore")

-- | A mapping specification producing edges of a specified label.
data EdgeSpec = 
  EdgeSpec {
    -- | The label of the target edges, which must conform to the edge type associated with that label.
    edgeSpecLabel :: PropertyGraph.EdgeLabel,
    -- | A specification of the id of each target edge
    edgeSpecId :: ValueSpec,
    -- | A specification of the out-vertex reference of each target edge
    edgeSpecOut :: ValueSpec,
    -- | A specification of the in-vertex reference of each target edge
    edgeSpecIn :: ValueSpec,
    -- | Zero or more property specifications for each target edge
    edgeSpecProperties :: [PropertySpec]}
  deriving (Eq, Ord, Read, Show)

_EdgeSpec = (Core.Name "hydra/langs/tinkerpop/mappings.EdgeSpec")

_EdgeSpec_label = (Core.Name "label")

_EdgeSpec_id = (Core.Name "id")

_EdgeSpec_out = (Core.Name "out")

_EdgeSpec_in = (Core.Name "in")

_EdgeSpec_properties = (Core.Name "properties")

-- | Either a vertex specification or an edge specification
data ElementSpec = 
  ElementSpecVertex VertexSpec |
  ElementSpecEdge EdgeSpec
  deriving (Eq, Ord, Read, Show)

_ElementSpec = (Core.Name "hydra/langs/tinkerpop/mappings.ElementSpec")

_ElementSpec_vertex = (Core.Name "vertex")

_ElementSpec_edge = (Core.Name "edge")

-- | A mapping specification producing properties of a specified key, and values of the appropriate type.
data PropertySpec = 
  PropertySpec {
    -- | The key of the target properties
    propertySpecKey :: PropertyGraph.PropertyKey,
    -- | A specification of the value of each target property, which must conform to the type associated with the property key
    propertySpecValue :: ValueSpec}
  deriving (Eq, Ord, Read, Show)

_PropertySpec = (Core.Name "hydra/langs/tinkerpop/mappings.PropertySpec")

_PropertySpec_key = (Core.Name "key")

_PropertySpec_value = (Core.Name "value")

-- | A set of mappings which translates between Hydra terms and annotations, and application-specific property graph types
data Schema s t v =
  Schema {
    schemaVertexIdTypes :: (Compute.Coder s s (Core.Type) t),
    schemaVertexIds :: (Compute.Coder s s (Core.Term) v),
    schemaEdgeIdTypes :: (Compute.Coder s s (Core.Type) t),
    schemaEdgeIds :: (Compute.Coder s s (Core.Term) v),
    schemaPropertyTypes :: (Compute.Coder s s (Core.Type) t),
    schemaPropertyValues :: (Compute.Coder s s (Core.Term) v),
    schemaAnnotations :: AnnotationSchema,
    schemaDefaultVertexId :: v,
    schemaDefaultEdgeId :: v}

_Schema = (Core.Name "hydra/langs/tinkerpop/mappings.Schema")

_Schema_vertexIdTypes = (Core.Name "vertexIdTypes")

_Schema_vertexIds = (Core.Name "vertexIds")

_Schema_edgeIdTypes = (Core.Name "edgeIdTypes")

_Schema_edgeIds = (Core.Name "edgeIds")

_Schema_propertyTypes = (Core.Name "propertyTypes")

_Schema_propertyValues = (Core.Name "propertyValues")

_Schema_annotations = (Core.Name "annotations")

_Schema_defaultVertexId = (Core.Name "defaultVertexId")

_Schema_defaultEdgeId = (Core.Name "defaultEdgeId")

-- | A mapping specification producing values (usually literal values) whose type is understood in context
data ValueSpec = 
  -- | A trivial no-op specification which passes the entire value
  ValueSpecValue  |
  -- | A compact path representing the function, e.g. engine-${engineInfo/model/name}
  ValueSpecPattern String
  deriving (Eq, Ord, Read, Show)

_ValueSpec = (Core.Name "hydra/langs/tinkerpop/mappings.ValueSpec")

_ValueSpec_value = (Core.Name "value")

_ValueSpec_pattern = (Core.Name "pattern")

-- | A mapping specification producing vertices of a specified label
data VertexSpec = 
  VertexSpec {
    -- | The label of the target vertices, which must conform to the vertex type associated with that label.
    vertexSpecLabel :: PropertyGraph.VertexLabel,
    -- | A specification of the id of each target vertex
    vertexSpecId :: ValueSpec,
    -- | Zero or more property specifications for each target vertex
    vertexSpecProperties :: [PropertySpec]}
  deriving (Eq, Ord, Read, Show)

_VertexSpec = (Core.Name "hydra/langs/tinkerpop/mappings.VertexSpec")

_VertexSpec_label = (Core.Name "label")

_VertexSpec_id = (Core.Name "id")

_VertexSpec_properties = (Core.Name "properties")
