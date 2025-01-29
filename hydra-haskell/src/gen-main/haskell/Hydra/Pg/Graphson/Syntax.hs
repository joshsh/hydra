-- | A syntax model for TinkerPop's GraphSON format. This model is designed to be as inclusive as possible, supporting GraphSON 4.0 as well as earlier versions. See https://github.com/apache/tinkerpop/blob/master/docs/src/dev/io/graphson.asciidoc.

module Hydra.Pg.Graphson.Syntax where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

newtype BigDecimalValue = 
  BigDecimalValue {
    unBigDecimalValue :: String}
  deriving (Eq, Ord, Read, Show)

_BigDecimalValue = (Core.Name "hydra/pg/graphson/syntax.BigDecimalValue")

data CompositeTypedValue = 
  CompositeTypedValue {
    compositeTypedValueType :: TypeName,
    compositeTypedValueFields :: Map_}
  deriving (Eq, Ord, Read, Show)

_CompositeTypedValue = (Core.Name "hydra/pg/graphson/syntax.CompositeTypedValue")

_CompositeTypedValue_type = (Core.Name "type")

_CompositeTypedValue_fields = (Core.Name "fields")

newtype DateTime = 
  DateTime {
    unDateTime :: String}
  deriving (Eq, Ord, Read, Show)

_DateTime = (Core.Name "hydra/pg/graphson/syntax.DateTime")

data DoubleValue = 
  DoubleValueFinite Double |
  DoubleValueInfinity  |
  DoubleValueNegativeInfinity  |
  DoubleValueNotANumber 
  deriving (Eq, Ord, Read, Show)

_DoubleValue = (Core.Name "hydra/pg/graphson/syntax.DoubleValue")

_DoubleValue_finite = (Core.Name "finite")

_DoubleValue_infinity = (Core.Name "infinity")

_DoubleValue_negativeInfinity = (Core.Name "negativeInfinity")

_DoubleValue_notANumber = (Core.Name "notANumber")

newtype Duration = 
  Duration {
    unDuration :: String}
  deriving (Eq, Ord, Read, Show)

_Duration = (Core.Name "hydra/pg/graphson/syntax.Duration")

newtype EdgeLabel = 
  EdgeLabel {
    unEdgeLabel :: String}
  deriving (Eq, Ord, Read, Show)

_EdgeLabel = (Core.Name "hydra/pg/graphson/syntax.EdgeLabel")

data FloatValue = 
  FloatValueFinite Float |
  FloatValueInfinity  |
  FloatValueNegativeInfinity  |
  FloatValueNotANumber 
  deriving (Eq, Ord, Read, Show)

_FloatValue = (Core.Name "hydra/pg/graphson/syntax.FloatValue")

_FloatValue_finite = (Core.Name "finite")

_FloatValue_infinity = (Core.Name "infinity")

_FloatValue_negativeInfinity = (Core.Name "negativeInfinity")

_FloatValue_notANumber = (Core.Name "notANumber")

newtype Map_ = 
  Map_ {
    unMap :: [ValuePair]}
  deriving (Eq, Ord, Read, Show)

_Map = (Core.Name "hydra/pg/graphson/syntax.Map")

data AdjacentEdge = 
  AdjacentEdge {
    adjacentEdgeId :: Value,
    adjacentEdgeVertexId :: Value,
    adjacentEdgeProperties :: (Map PropertyKey Value)}
  deriving (Eq, Ord, Read, Show)

_AdjacentEdge = (Core.Name "hydra/pg/graphson/syntax.AdjacentEdge")

_AdjacentEdge_id = (Core.Name "id")

_AdjacentEdge_vertexId = (Core.Name "vertexId")

_AdjacentEdge_properties = (Core.Name "properties")

data PrimitiveTypedValue = 
  PrimitiveTypedValue {
    primitiveTypedValueType :: TypeName,
    primitiveTypedValueValue :: String}
  deriving (Eq, Ord, Read, Show)

_PrimitiveTypedValue = (Core.Name "hydra/pg/graphson/syntax.PrimitiveTypedValue")

_PrimitiveTypedValue_type = (Core.Name "type")

_PrimitiveTypedValue_value = (Core.Name "value")

newtype PropertyKey = 
  PropertyKey {
    unPropertyKey :: String}
  deriving (Eq, Ord, Read, Show)

_PropertyKey = (Core.Name "hydra/pg/graphson/syntax.PropertyKey")

newtype TypeName = 
  TypeName {
    unTypeName :: String}
  deriving (Eq, Ord, Read, Show)

_TypeName = (Core.Name "hydra/pg/graphson/syntax.TypeName")

newtype Uuid = 
  Uuid {
    unUuid :: String}
  deriving (Eq, Ord, Read, Show)

_Uuid = (Core.Name "hydra/pg/graphson/syntax.Uuid")

data Value = 
  ValueBigDecimal BigDecimalValue |
  ValueBigInteger Integer |
  ValueBinary String |
  ValueBoolean Bool |
  ValueByte Int16 |
  ValueChar Int64 |
  ValueComposite CompositeTypedValue |
  ValueDateTime DateTime |
  ValueDouble DoubleValue |
  ValueDuration Duration |
  ValueFloat FloatValue |
  ValueInteger Int |
  ValueList [Value] |
  ValueLong Int64 |
  ValueMap Map_ |
  ValueNull  |
  ValuePrimitive PrimitiveTypedValue |
  ValueSet [Value] |
  ValueShort Int16 |
  ValueString String |
  ValueUuid Uuid
  deriving (Eq, Ord, Read, Show)

_Value = (Core.Name "hydra/pg/graphson/syntax.Value")

_Value_bigDecimal = (Core.Name "bigDecimal")

_Value_bigInteger = (Core.Name "bigInteger")

_Value_binary = (Core.Name "binary")

_Value_boolean = (Core.Name "boolean")

_Value_byte = (Core.Name "byte")

_Value_char = (Core.Name "char")

_Value_composite = (Core.Name "composite")

_Value_dateTime = (Core.Name "dateTime")

_Value_double = (Core.Name "double")

_Value_duration = (Core.Name "duration")

_Value_float = (Core.Name "float")

_Value_integer = (Core.Name "integer")

_Value_list = (Core.Name "list")

_Value_long = (Core.Name "long")

_Value_map = (Core.Name "map")

_Value_null = (Core.Name "null")

_Value_primitive = (Core.Name "primitive")

_Value_set = (Core.Name "set")

_Value_short = (Core.Name "short")

_Value_string = (Core.Name "string")

_Value_uuid = (Core.Name "uuid")

data ValuePair = 
  ValuePair {
    valuePairFirst :: Value,
    valuePairSecond :: Value}
  deriving (Eq, Ord, Read, Show)

_ValuePair = (Core.Name "hydra/pg/graphson/syntax.ValuePair")

_ValuePair_first = (Core.Name "first")

_ValuePair_second = (Core.Name "second")

data Vertex = 
  Vertex {
    vertexId :: Value,
    vertexLabel :: (Maybe VertexLabel),
    vertexInEdges :: (Map EdgeLabel [AdjacentEdge]),
    vertexOutEdges :: (Map EdgeLabel [AdjacentEdge]),
    vertexProperties :: (Map PropertyKey [VertexPropertyValue])}
  deriving (Eq, Ord, Read, Show)

_Vertex = (Core.Name "hydra/pg/graphson/syntax.Vertex")

_Vertex_id = (Core.Name "id")

_Vertex_label = (Core.Name "label")

_Vertex_inEdges = (Core.Name "inEdges")

_Vertex_outEdges = (Core.Name "outEdges")

_Vertex_properties = (Core.Name "properties")

newtype VertexLabel = 
  VertexLabel {
    unVertexLabel :: String}
  deriving (Eq, Ord, Read, Show)

_VertexLabel = (Core.Name "hydra/pg/graphson/syntax.VertexLabel")

data VertexPropertyValue = 
  VertexPropertyValue {
    vertexPropertyValueId :: (Maybe Value),
    vertexPropertyValueValue :: Value}
  deriving (Eq, Ord, Read, Show)

_VertexPropertyValue = (Core.Name "hydra/pg/graphson/syntax.VertexPropertyValue")

_VertexPropertyValue_id = (Core.Name "id")

_VertexPropertyValue_value = (Core.Name "value")