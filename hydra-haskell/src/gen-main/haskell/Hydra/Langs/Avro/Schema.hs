-- | A model for Avro schemas. Based on the Avro 1.11.1 specification:
-- |   https://avro.apache.org/docs/1.11.1/specification

module Hydra.Langs.Avro.Schema where

import qualified Hydra.Core as Core
import qualified Hydra.Json as Json
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

data Array = 
  Array {
    arrayItems :: Schema}
  deriving (Eq, Ord, Read, Show)

_Array = (Core.Name "hydra/langs/avro/schema.Array")

_Array_items = (Core.Name "items")

data Enum_ = 
  Enum_ {
    -- | a JSON array, listing symbols, as JSON strings. All symbols in an enum must be unique; duplicates are prohibited. Every symbol must match the regular expression [A-Za-z_][A-Za-z0-9_]* (the same requirement as for names)
    enumSymbols :: [String],
    -- | A default value for this enumeration, used during resolution when the reader encounters a symbol from the writer that isn’t defined in the reader’s schema. The value provided here must be a JSON string that’s a member of the symbols array
    enumDefault :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Enum = (Core.Name "hydra/langs/avro/schema.Enum")

_Enum_symbols = (Core.Name "symbols")

_Enum_default = (Core.Name "default")

data Field = 
  Field {
    -- | a JSON string providing the name of the field
    fieldName :: String,
    -- | a JSON string describing this field for users
    fieldDoc :: (Maybe String),
    -- | a schema
    fieldType :: Schema,
    -- | default value for this field, only used when reading instances that lack the field for schema evolution purposes
    fieldDefault :: (Maybe Json.Value),
    -- | specifies how this field impacts sort ordering of this record
    fieldOrder :: (Maybe Order),
    -- | a JSON array of strings, providing alternate names for this field
    fieldAliases :: (Maybe [String]),
    -- | Any additional key/value pairs attached to the field
    fieldAnnotations :: (Map String Json.Value)}
  deriving (Eq, Ord, Read, Show)

_Field = (Core.Name "hydra/langs/avro/schema.Field")

_Field_name = (Core.Name "name")

_Field_doc = (Core.Name "doc")

_Field_type = (Core.Name "type")

_Field_default = (Core.Name "default")

_Field_order = (Core.Name "order")

_Field_aliases = (Core.Name "aliases")

_Field_annotations = (Core.Name "annotations")

data Fixed = 
  Fixed {
    -- | an integer, specifying the number of bytes per value
    fixedSize :: Int}
  deriving (Eq, Ord, Read, Show)

_Fixed = (Core.Name "hydra/langs/avro/schema.Fixed")

_Fixed_size = (Core.Name "size")

data Map_ = 
  Map_ {
    mapValues :: Schema}
  deriving (Eq, Ord, Read, Show)

_Map = (Core.Name "hydra/langs/avro/schema.Map")

_Map_values = (Core.Name "values")

data Named = 
  Named {
    -- | a string naming this schema
    namedName :: String,
    -- | a string that qualifies the name
    namedNamespace :: (Maybe String),
    -- | a JSON array of strings, providing alternate names for this schema
    namedAliases :: (Maybe [String]),
    -- | a JSON string providing documentation to the user of this schema
    namedDoc :: (Maybe String),
    namedType :: NamedType,
    -- | Any additional key/value pairs attached to the type
    namedAnnotations :: (Map String Json.Value)}
  deriving (Eq, Ord, Read, Show)

_Named = (Core.Name "hydra/langs/avro/schema.Named")

_Named_name = (Core.Name "name")

_Named_namespace = (Core.Name "namespace")

_Named_aliases = (Core.Name "aliases")

_Named_doc = (Core.Name "doc")

_Named_type = (Core.Name "type")

_Named_annotations = (Core.Name "annotations")

data NamedType = 
  NamedTypeEnum Enum_ |
  NamedTypeFixed Fixed |
  NamedTypeRecord Record
  deriving (Eq, Ord, Read, Show)

_NamedType = (Core.Name "hydra/langs/avro/schema.NamedType")

_NamedType_enum = (Core.Name "enum")

_NamedType_fixed = (Core.Name "fixed")

_NamedType_record = (Core.Name "record")

data Order = 
  OrderAscending  |
  OrderDescending  |
  OrderIgnore 
  deriving (Eq, Ord, Read, Show)

_Order = (Core.Name "hydra/langs/avro/schema.Order")

_Order_ascending = (Core.Name "ascending")

_Order_descending = (Core.Name "descending")

_Order_ignore = (Core.Name "ignore")

data Primitive = 
  -- | no value
  PrimitiveNull  |
  -- | A binary value
  PrimitiveBoolean  |
  -- | 32-bit signed integer
  PrimitiveInt  |
  -- | 64-bit signed integer
  PrimitiveLong  |
  -- | single precision (32-bit) IEEE 754 floating-point number
  PrimitiveFloat  |
  -- | double precision (64-bit) IEEE 754 floating-point number
  PrimitiveDouble  |
  -- | sequence of 8-bit unsigned bytes
  PrimitiveBytes  |
  -- | unicode character sequence
  PrimitiveString 
  deriving (Eq, Ord, Read, Show)

_Primitive = (Core.Name "hydra/langs/avro/schema.Primitive")

_Primitive_null = (Core.Name "null")

_Primitive_boolean = (Core.Name "boolean")

_Primitive_int = (Core.Name "int")

_Primitive_long = (Core.Name "long")

_Primitive_float = (Core.Name "float")

_Primitive_double = (Core.Name "double")

_Primitive_bytes = (Core.Name "bytes")

_Primitive_string = (Core.Name "string")

data Record = 
  Record {
    -- | a JSON array, listing fields
    recordFields :: [Field]}
  deriving (Eq, Ord, Read, Show)

_Record = (Core.Name "hydra/langs/avro/schema.Record")

_Record_fields = (Core.Name "fields")

data Schema = 
  SchemaArray Array |
  SchemaMap Map_ |
  SchemaNamed Named |
  SchemaPrimitive Primitive |
  -- | A reference by name to a previously defined type
  SchemaReference String |
  SchemaUnion Union
  deriving (Eq, Ord, Read, Show)

_Schema = (Core.Name "hydra/langs/avro/schema.Schema")

_Schema_array = (Core.Name "array")

_Schema_map = (Core.Name "map")

_Schema_named = (Core.Name "named")

_Schema_primitive = (Core.Name "primitive")

_Schema_reference = (Core.Name "reference")

_Schema_union = (Core.Name "union")

newtype Union = 
  Union {
    unUnion :: [Schema]}
  deriving (Eq, Ord, Read, Show)

_Union = (Core.Name "hydra/langs/avro/schema.Union")
