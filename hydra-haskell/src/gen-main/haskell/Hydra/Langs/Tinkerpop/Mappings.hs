-- | A model for property graph mapping specifications

module Hydra.Langs.Tinkerpop.Mappings where

import qualified Hydra.Compute as Compute
import qualified Hydra.Core as Core
import qualified Hydra.Langs.Tinkerpop.PropertyGraph as PropertyGraph
import Data.List
import Data.Map
import Data.Set

-- | Configurable annotations for property graph mapping specifications
data AnnotationSchema = 
  AnnotationSchema {
    annotationSchemaVertexId :: String,
    annotationSchemaEdgeId :: String,
    annotationSchemaOutVertex :: String,
    annotationSchemaInVertex :: String,
    annotationSchemaVertexLabel :: String,
    annotationSchemaEdgeLabel :: String,
    annotationSchemaIgnore :: String}
  deriving (Eq, Ord, Read, Show)

_AnnotationSchema = (Core.Name "hydra/langs/tinkerpop/mappings.AnnotationSchema")

_AnnotationSchema_vertexId = (Core.FieldName "vertexId")

_AnnotationSchema_edgeId = (Core.FieldName "edgeId")

_AnnotationSchema_outVertex = (Core.FieldName "outVertex")

_AnnotationSchema_inVertex = (Core.FieldName "inVertex")

_AnnotationSchema_vertexLabel = (Core.FieldName "vertexLabel")

_AnnotationSchema_edgeLabel = (Core.FieldName "edgeLabel")

_AnnotationSchema_ignore = (Core.FieldName "ignore")

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

_EdgeSpec_label = (Core.FieldName "label")

_EdgeSpec_id = (Core.FieldName "id")

_EdgeSpec_out = (Core.FieldName "out")

_EdgeSpec_in = (Core.FieldName "in")

_EdgeSpec_properties = (Core.FieldName "properties")

-- | Either a vertex specification or an edge specification
data ElementSpec = 
  ElementSpecVertex VertexSpec |
  ElementSpecEdge EdgeSpec
  deriving (Eq, Ord, Read, Show)

_ElementSpec = (Core.Name "hydra/langs/tinkerpop/mappings.ElementSpec")

_ElementSpec_vertex = (Core.FieldName "vertex")

_ElementSpec_edge = (Core.FieldName "edge")

-- | A mapping specification producing properties of a specified key, and values of the appropriate type.
data PropertySpec = 
  PropertySpec {
    -- | The key of the target properties
    propertySpecKey :: PropertyGraph.PropertyKey,
    -- | A specification of the value of each target property, which must conform to the type associated with the property key
    propertySpecValue :: ValueSpec}
  deriving (Eq, Ord, Read, Show)

_PropertySpec = (Core.Name "hydra/langs/tinkerpop/mappings.PropertySpec")

_PropertySpec_key = (Core.FieldName "key")

_PropertySpec_value = (Core.FieldName "value")

data Schema s a t v e p = 
  Schema {
    schemaVertexIds :: (Compute.Coder s s (Core.Term a) v),
    schemaEdgeIds :: (Compute.Coder s s (Core.Term a) e),
    schemaPropertyTypes :: (Compute.Coder s s (Core.Type a) t),
    schemaPropertyValues :: (Compute.Coder s s (Core.Term a) p),
    schemaAnnotations :: AnnotationSchema}

_Schema = (Core.Name "hydra/langs/tinkerpop/mappings.Schema")

_Schema_vertexIds = (Core.FieldName "vertexIds")

_Schema_edgeIds = (Core.FieldName "edgeIds")

_Schema_propertyTypes = (Core.FieldName "propertyTypes")

_Schema_propertyValues = (Core.FieldName "propertyValues")

_Schema_annotations = (Core.FieldName "annotations")

-- | A mapping specification producing values (usually literal values) whose type is understood in context
data ValueSpec = 
  -- | A trivial no-op specification which passes the entire value
  ValueSpecValue  |
  -- | A compact path representing the function, e.g. ${}/engineInfo/model/name
  ValueSpecPattern String
  deriving (Eq, Ord, Read, Show)

_ValueSpec = (Core.Name "hydra/langs/tinkerpop/mappings.ValueSpec")

_ValueSpec_value = (Core.FieldName "value")

_ValueSpec_pattern = (Core.FieldName "pattern")

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

_VertexSpec_label = (Core.FieldName "label")

_VertexSpec_id = (Core.FieldName "id")

_VertexSpec_properties = (Core.FieldName "properties")