-- | A model for Protocol Buffers v3 enum and message types, designed as a target for transformations.This model is loosely based on https://github.com/protocolbuffers/protobuf/blob/main/src/google/protobuf/type.proto, as well as the proto3 reference documentation

module Hydra.Langs.Protobuf.Proto3 where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

data Definition = 
  DefinitionEnum EnumDefinition |
  DefinitionMessage MessageDefinition
  deriving (Eq, Ord, Read, Show)

_Definition = (Core.Name "hydra/langs/protobuf/proto3.Definition")

_Definition_enum = (Core.Name "enum")

_Definition_message = (Core.Name "message")

-- | Enum type definition
data EnumDefinition = 
  EnumDefinition {
    -- | Enum type name
    enumDefinitionName :: TypeName,
    -- | Enum value definitions
    enumDefinitionValues :: [EnumValue],
    -- | Protocol buffer options
    enumDefinitionOptions :: [Option]}
  deriving (Eq, Ord, Read, Show)

_EnumDefinition = (Core.Name "hydra/langs/protobuf/proto3.EnumDefinition")

_EnumDefinition_name = (Core.Name "name")

_EnumDefinition_values = (Core.Name "values")

_EnumDefinition_options = (Core.Name "options")

-- | Enum value definition
data EnumValue = 
  EnumValue {
    -- | Enum value name
    enumValueName :: EnumValueName,
    -- | Enum value number
    enumValueNumber :: Int,
    -- | Protocol buffer options
    enumValueOptions :: [Option]}
  deriving (Eq, Ord, Read, Show)

_EnumValue = (Core.Name "hydra/langs/protobuf/proto3.EnumValue")

_EnumValue_name = (Core.Name "name")

_EnumValue_number = (Core.Name "number")

_EnumValue_options = (Core.Name "options")

newtype EnumValueName = 
  EnumValueName {
    unEnumValueName :: String}
  deriving (Eq, Ord, Read, Show)

_EnumValueName = (Core.Name "hydra/langs/protobuf/proto3.EnumValueName")

-- | A single field of a message type
data Field = 
  Field {
    -- | The field name
    fieldName :: FieldName,
    -- | The field JSON name
    fieldJsonName :: (Maybe String),
    -- | The datatype of the field
    fieldType :: FieldType,
    -- | The field number
    fieldNumber :: Int,
    -- | The protocol buffer options
    fieldOptions :: [Option]}
  deriving (Eq, Ord, Read, Show)

_Field = (Core.Name "hydra/langs/protobuf/proto3.Field")

_Field_name = (Core.Name "name")

_Field_jsonName = (Core.Name "jsonName")

_Field_type = (Core.Name "type")

_Field_number = (Core.Name "number")

_Field_options = (Core.Name "options")

-- | The name of a field
newtype FieldName = 
  FieldName {
    -- | The name of a field
    unFieldName :: String}
  deriving (Eq, Ord, Read, Show)

_FieldName = (Core.Name "hydra/langs/protobuf/proto3.FieldName")

data FieldType = 
  FieldTypeMap SimpleType |
  FieldTypeOneof [Field] |
  FieldTypeRepeated SimpleType |
  FieldTypeSimple SimpleType
  deriving (Eq, Ord, Read, Show)

_FieldType = (Core.Name "hydra/langs/protobuf/proto3.FieldType")

_FieldType_map = (Core.Name "map")

_FieldType_oneof = (Core.Name "oneof")

_FieldType_repeated = (Core.Name "repeated")

_FieldType_simple = (Core.Name "simple")

newtype FileReference = 
  FileReference {
    unFileReference :: String}
  deriving (Eq, Ord, Read, Show)

_FileReference = (Core.Name "hydra/langs/protobuf/proto3.FileReference")

-- | A protocol buffer message type
data MessageDefinition = 
  MessageDefinition {
    -- | The fully qualified message name
    messageDefinitionName :: TypeName,
    -- | The list of fields
    messageDefinitionFields :: [Field],
    -- | The protocol buffer options
    messageDefinitionOptions :: [Option]}
  deriving (Eq, Ord, Read, Show)

_MessageDefinition = (Core.Name "hydra/langs/protobuf/proto3.MessageDefinition")

_MessageDefinition_name = (Core.Name "name")

_MessageDefinition_fields = (Core.Name "fields")

_MessageDefinition_options = (Core.Name "options")

-- | A protocol buffer option, which can be attached to a message, field, enumeration, etc
data Option = 
  Option {
    -- | The option's name. For protobuf built-in options (options defined in descriptor.proto), this is the short name. For example, `"map_entry"`. For custom options, it should be the fully-qualified name. For example, `"google.api.http"`.
    optionName :: String,
    -- | The option's value
    optionValue :: String}
  deriving (Eq, Ord, Read, Show)

_Option = (Core.Name "hydra/langs/protobuf/proto3.Option")

_Option_name = (Core.Name "name")

_Option_value = (Core.Name "value")

newtype PackageName = 
  PackageName {
    unPackageName :: String}
  deriving (Eq, Ord, Read, Show)

_PackageName = (Core.Name "hydra/langs/protobuf/proto3.PackageName")

-- | A .proto file, usually containing one or more enum or message type definitions
data ProtoFile = 
  ProtoFile {
    protoFilePackage :: PackageName,
    protoFileImports :: [FileReference],
    protoFileTypes :: [Definition],
    protoFileOptions :: [Option]}
  deriving (Eq, Ord, Read, Show)

_ProtoFile = (Core.Name "hydra/langs/protobuf/proto3.ProtoFile")

_ProtoFile_package = (Core.Name "package")

_ProtoFile_imports = (Core.Name "imports")

_ProtoFile_types = (Core.Name "types")

_ProtoFile_options = (Core.Name "options")

-- | One of several Proto3 scalar types
data ScalarType = 
  ScalarTypeBool  |
  ScalarTypeBytes  |
  ScalarTypeDouble  |
  ScalarTypeFixed32  |
  ScalarTypeFixed64  |
  ScalarTypeFloat  |
  ScalarTypeInt32  |
  ScalarTypeInt64  |
  ScalarTypeSfixed32  |
  ScalarTypeSfixed64  |
  ScalarTypeSint32  |
  ScalarTypeSint64  |
  ScalarTypeString  |
  ScalarTypeUint32  |
  ScalarTypeUint64 
  deriving (Eq, Ord, Read, Show)

_ScalarType = (Core.Name "hydra/langs/protobuf/proto3.ScalarType")

_ScalarType_bool = (Core.Name "bool")

_ScalarType_bytes = (Core.Name "bytes")

_ScalarType_double = (Core.Name "double")

_ScalarType_fixed32 = (Core.Name "fixed32")

_ScalarType_fixed64 = (Core.Name "fixed64")

_ScalarType_float = (Core.Name "float")

_ScalarType_int32 = (Core.Name "int32")

_ScalarType_int64 = (Core.Name "int64")

_ScalarType_sfixed32 = (Core.Name "sfixed32")

_ScalarType_sfixed64 = (Core.Name "sfixed64")

_ScalarType_sint32 = (Core.Name "sint32")

_ScalarType_sint64 = (Core.Name "sint64")

_ScalarType_string = (Core.Name "string")

_ScalarType_uint32 = (Core.Name "uint32")

_ScalarType_uint64 = (Core.Name "uint64")

-- | A scalar type or a reference to an enum type or message type
data SimpleType = 
  SimpleTypeReference TypeName |
  SimpleTypeScalar ScalarType
  deriving (Eq, Ord, Read, Show)

_SimpleType = (Core.Name "hydra/langs/protobuf/proto3.SimpleType")

_SimpleType_reference = (Core.Name "reference")

_SimpleType_scalar = (Core.Name "scalar")

-- | The local name of an enum type or message type
newtype TypeName = 
  TypeName {
    -- | The local name of an enum type or message type
    unTypeName :: String}
  deriving (Eq, Ord, Read, Show)

_TypeName = (Core.Name "hydra/langs/protobuf/proto3.TypeName")

-- | A reference to an enum type or message type
newtype TypeReference = 
  TypeReference {
    -- | A reference to an enum type or message type
    unTypeReference :: String}
  deriving (Eq, Ord, Read, Show)

_TypeReference = (Core.Name "hydra/langs/protobuf/proto3.TypeReference")
