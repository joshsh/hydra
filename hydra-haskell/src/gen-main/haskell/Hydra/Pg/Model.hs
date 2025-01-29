-- | A typed property graph data model. Property graphs are parameterized a type for property and id values, while property graph schemas are parameterized by a type for property and id types

module Hydra.Pg.Model where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | An edge which is adjacent to a given vertex. Only the other endpoint of the edge is provided.
data AdjacentEdge v = 
  AdjacentEdge {
    -- | The label of the edge
    adjacentEdgeLabel :: EdgeLabel,
    -- | The unique identifier of the edge
    adjacentEdgeId :: v,
    -- | The id of the other vertex adjacent to the edge
    adjacentEdgeVertex :: v,
    -- | A key/value map of edge properties
    adjacentEdgeProperties :: (Map PropertyKey v)}
  deriving (Eq, Ord, Read, Show)

_AdjacentEdge = (Core.Name "hydra/pg/model.AdjacentEdge")

_AdjacentEdge_label = (Core.Name "label")

_AdjacentEdge_id = (Core.Name "id")

_AdjacentEdge_vertex = (Core.Name "vertex")

_AdjacentEdge_properties = (Core.Name "properties")

-- | The direction of an edge or edge pattern
data Direction = 
  DirectionOut  |
  DirectionIn  |
  DirectionBoth  |
  DirectionUndirected 
  deriving (Eq, Ord, Read, Show)

_Direction = (Core.Name "hydra/pg/model.Direction")

_Direction_out = (Core.Name "out")

_Direction_in = (Core.Name "in")

_Direction_both = (Core.Name "both")

_Direction_undirected = (Core.Name "undirected")

-- | An edge
data Edge v = 
  Edge {
    -- | The label of the edge
    edgeLabel :: EdgeLabel,
    -- | The unique identifier of the edge
    edgeId :: v,
    -- | The id of the out-vertex (tail) of the edge
    edgeOut :: v,
    -- | The id of the in-vertex (head) of the edge
    edgeIn :: v,
    -- | A key/value map of edge properties
    edgeProperties :: (Map PropertyKey v)}
  deriving (Eq, Ord, Read, Show)

_Edge = (Core.Name "hydra/pg/model.Edge")

_Edge_label = (Core.Name "label")

_Edge_id = (Core.Name "id")

_Edge_out = (Core.Name "out")

_Edge_in = (Core.Name "in")

_Edge_properties = (Core.Name "properties")

-- | The label of an edge
newtype EdgeLabel = 
  EdgeLabel {
    unEdgeLabel :: String}
  deriving (Eq, Ord, Read, Show)

_EdgeLabel = (Core.Name "hydra/pg/model.EdgeLabel")

-- | The type of an edge
data EdgeType t = 
  EdgeType {
    -- | The label of any edge of this edge type
    edgeTypeLabel :: EdgeLabel,
    -- | The type of the id of any edge of this edge type
    edgeTypeId :: t,
    -- | The label of the out-vertex (tail) of any edge of this edge type
    edgeTypeOut :: VertexLabel,
    -- | The label of the in-vertex (head) of any edge of this edge type
    edgeTypeIn :: VertexLabel,
    -- | A list of property types. The types are ordered for the sake of applications in which property order is significant.
    edgeTypeProperties :: [PropertyType t]}
  deriving (Eq, Ord, Read, Show)

_EdgeType = (Core.Name "hydra/pg/model.EdgeType")

_EdgeType_label = (Core.Name "label")

_EdgeType_id = (Core.Name "id")

_EdgeType_out = (Core.Name "out")

_EdgeType_in = (Core.Name "in")

_EdgeType_properties = (Core.Name "properties")

-- | Either a vertex or an edge
data Element v = 
  ElementVertex (Vertex v) |
  ElementEdge (Edge v)
  deriving (Eq, Ord, Read, Show)

_Element = (Core.Name "hydra/pg/model.Element")

_Element_vertex = (Core.Name "vertex")

_Element_edge = (Core.Name "edge")

-- | The kind of an element: vertex or edge
data ElementKind = 
  ElementKindVertex  |
  ElementKindEdge 
  deriving (Eq, Ord, Read, Show)

_ElementKind = (Core.Name "hydra/pg/model.ElementKind")

_ElementKind_vertex = (Core.Name "vertex")

_ElementKind_edge = (Core.Name "edge")

-- | An element together with its dependencies in some context
data ElementTree v = 
  ElementTree {
    elementTreeSelf :: (Element v),
    elementTreeDependencies :: [ElementTree v]}
  deriving (Eq, Ord, Read, Show)

_ElementTree = (Core.Name "hydra/pg/model.ElementTree")

_ElementTree_self = (Core.Name "self")

_ElementTree_dependencies = (Core.Name "dependencies")

-- | The type of a vertex or edge
data ElementType t = 
  ElementTypeVertex (VertexType t) |
  ElementTypeEdge (EdgeType t)
  deriving (Eq, Ord, Read, Show)

_ElementType = (Core.Name "hydra/pg/model.ElementType")

_ElementType_vertex = (Core.Name "vertex")

_ElementType_edge = (Core.Name "edge")

-- | An element type together with its dependencies in some context
data ElementTypeTree t = 
  ElementTypeTree {
    elementTypeTreeSelf :: (ElementType t),
    elementTypeTreeDependencies :: [ElementTypeTree t]}
  deriving (Eq, Ord, Read, Show)

_ElementTypeTree = (Core.Name "hydra/pg/model.ElementTypeTree")

_ElementTypeTree_self = (Core.Name "self")

_ElementTypeTree_dependencies = (Core.Name "dependencies")

-- | A graph; a self-contained collection of vertices and edges
data Graph v = 
  Graph {
    graphVertices :: (Map v (Vertex v)),
    graphEdges :: (Map v (Edge v))}
  deriving (Eq, Ord, Read, Show)

_Graph = (Core.Name "hydra/pg/model.Graph")

_Graph_vertices = (Core.Name "vertices")

_Graph_edges = (Core.Name "edges")

-- | A graph schema; a vertex and edge types for the vertices and edges of a graph conforming to the schema
data GraphSchema t = 
  GraphSchema {
    -- | A unique vertex type for each vertex label which may occur in a graph
    graphSchemaVertices :: (Map VertexLabel (VertexType t)),
    -- | A unique edge type for each edge label which may occur in a graph
    graphSchemaEdges :: (Map EdgeLabel (EdgeType t))}
  deriving (Eq, Ord, Read, Show)

_GraphSchema = (Core.Name "hydra/pg/model.GraphSchema")

_GraphSchema_vertices = (Core.Name "vertices")

_GraphSchema_edges = (Core.Name "edges")

-- | Either a vertex or edge label
data Label = 
  LabelVertex VertexLabel |
  LabelEdge EdgeLabel
  deriving (Eq, Ord, Read, Show)

_Label = (Core.Name "hydra/pg/model.Label")

_Label_vertex = (Core.Name "vertex")

_Label_edge = (Core.Name "edge")

-- | A key/value property
data Property v = 
  Property {
    -- | They key of the property
    propertyKey :: PropertyKey,
    -- | The value of the property
    propertyValue :: v}
  deriving (Eq, Ord, Read, Show)

_Property = (Core.Name "hydra/pg/model.Property")

_Property_key = (Core.Name "key")

_Property_value = (Core.Name "value")

-- | A property key
newtype PropertyKey = 
  PropertyKey {
    unPropertyKey :: String}
  deriving (Eq, Ord, Read, Show)

_PropertyKey = (Core.Name "hydra/pg/model.PropertyKey")

-- | The type of a property
data PropertyType t = 
  PropertyType {
    -- | A property's key
    propertyTypeKey :: PropertyKey,
    -- | The type of a property's value
    propertyTypeValue :: t,
    -- | Whether the property is required; values may be omitted from a property map otherwise
    propertyTypeRequired :: Bool}
  deriving (Eq, Ord, Read, Show)

_PropertyType = (Core.Name "hydra/pg/model.PropertyType")

_PropertyType_key = (Core.Name "key")

_PropertyType_value = (Core.Name "value")

_PropertyType_required = (Core.Name "required")

-- | A vertex
data Vertex v = 
  Vertex {
    -- | The label of the vertex
    vertexLabel :: VertexLabel,
    -- | The unique identifier of the vertex
    vertexId :: v,
    -- | A key/value map of vertex properties
    vertexProperties :: (Map PropertyKey v)}
  deriving (Eq, Ord, Read, Show)

_Vertex = (Core.Name "hydra/pg/model.Vertex")

_Vertex_label = (Core.Name "label")

_Vertex_id = (Core.Name "id")

_Vertex_properties = (Core.Name "properties")

-- | The label of a vertex. The default (null) vertex is represented by the empty string
newtype VertexLabel = 
  VertexLabel {
    unVertexLabel :: String}
  deriving (Eq, Ord, Read, Show)

_VertexLabel = (Core.Name "hydra/pg/model.VertexLabel")

-- | The type of a vertex
data VertexType t = 
  VertexType {
    -- | The label of any vertex of this vertex type
    vertexTypeLabel :: VertexLabel,
    -- | The type of the id of any vertex of this vertex type
    vertexTypeId :: t,
    -- | A list of property types. The types are ordered for the sake of applications in which property order is significant.
    vertexTypeProperties :: [PropertyType t]}
  deriving (Eq, Ord, Read, Show)

_VertexType = (Core.Name "hydra/pg/model.VertexType")

_VertexType_label = (Core.Name "label")

_VertexType_id = (Core.Name "id")

_VertexType_properties = (Core.Name "properties")

-- | A vertex together with any outgoing and/or incoming edges; a vertex object
data VertexWithAdjacentEdges v = 
  VertexWithAdjacentEdges {
    -- | The focus vertex
    vertexWithAdjacentEdgesVertex :: (Vertex v),
    -- | An adjacency list of edges in which the focus vertex is the head (in-vertex) of the edge
    vertexWithAdjacentEdgesIns :: [AdjacentEdge v],
    -- | An adjacency list of edges in which the focus vertex is the tail (out-vertex) of the edge
    vertexWithAdjacentEdgesOuts :: [AdjacentEdge v]}
  deriving (Eq, Ord, Read, Show)

_VertexWithAdjacentEdges = (Core.Name "hydra/pg/model.VertexWithAdjacentEdges")

_VertexWithAdjacentEdges_vertex = (Core.Name "vertex")

_VertexWithAdjacentEdges_ins = (Core.Name "ins")

_VertexWithAdjacentEdges_outs = (Core.Name "outs")