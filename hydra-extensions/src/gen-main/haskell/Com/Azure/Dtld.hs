-- | An Azure Digital Twin Definition Language (DTLD) model. Based on:
-- |   https://github.com/Azure/opendigitaltwins-dtdl/blob/master/DTDL/v2/dtdlv2.md#digital-twins-definition-language
-- | DTLD features which are not currently included in this model:
-- |   * geospatial schemas (https://github.com/Azure/opendigitaltwins-dtdl/blob/master/DTDL/v2/dtdlv2.md#geospatial-schemas)
-- |   * semantic types and units (https://github.com/Azure/opendigitaltwins-dtdl/blob/master/DTDL/v2/dtdlv2.md#semantic-types)
-- |   * model versioning (https://github.com/Azure/opendigitaltwins-dtdl/blob/master/DTDL/v2/dtdlv2.md#model-versioning)

module Com.Azure.Dtld where

import qualified Hydra.Core as Core
import Data.List
import Data.Map
import Data.Set

-- | A Command describes a function or operation that can be performed on any digital twin.
data Command = 
  Command {
    -- | This must be 'Command'
    commandType :: Iri,
    -- | The 'programming' name of the command. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.
    commandName :: String,
    -- | The ID of the command. If no @id is provided, the digital twin interface processor will assign one.
    commandId :: (Maybe Dtmi),
    -- | A comment for model authors
    commandComment :: (Maybe String),
    -- | A localizable description for display
    commandDescription :: (Maybe String),
    -- | A localizable name for display
    commandDisplayName :: (Maybe String),
    -- | This property is deprecated. Either value, synchronous or asynchronous, has the same meaning: a command that starts execution within a configurable time and that completes execution within a configurable time.
    commandCommandType :: (Maybe CommandType),
    -- | A description of the input to the Command
    commandRequest :: (Maybe CommandPayload),
    -- | A description of the output of the Command
    commandResponse :: (Maybe CommandPayload)}
  deriving (Eq, Ord, Read, Show)

_Command = (Core.Name "com/azure/dtld.Command")

_Command_type = (Core.Name "type")

_Command_name = (Core.Name "name")

_Command_id = (Core.Name "id")

_Command_comment = (Core.Name "comment")

_Command_description = (Core.Name "description")

_Command_displayName = (Core.Name "displayName")

_Command_commandType = (Core.Name "commandType")

_Command_request = (Core.Name "request")

_Command_response = (Core.Name "response")

-- | A CommandPayload describes the inputs to or the outputs from a Command.
data CommandPayload = 
  CommandPayload {
    -- | The 'programming' name of the payload. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.
    commandPayloadName :: String,
    -- | The data type of the payload
    commandPayloadSchema :: Schema,
    -- | The ID of the payload. If no @id is provided, the digital twin interface processor will assign one.
    commandPayloadId :: (Maybe Dtmi),
    -- | A comment for model authors
    commandPayloadComment :: (Maybe String),
    -- | A localizable description for display
    commandPayloadDescription :: (Maybe String),
    -- | A localizable name for display
    commandPayloadDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_CommandPayload = (Core.Name "com/azure/dtld.CommandPayload")

_CommandPayload_name = (Core.Name "name")

_CommandPayload_schema = (Core.Name "schema")

_CommandPayload_id = (Core.Name "id")

_CommandPayload_comment = (Core.Name "comment")

_CommandPayload_description = (Core.Name "description")

_CommandPayload_displayName = (Core.Name "displayName")

-- | CommandType is deprecated. Either value, synchronous or asynchronous, has the same meaning: a command that starts execution within a configurable time and that completes execution within a configurable time.
data CommandType = 
  CommandTypeSynchronous  |
  CommandTypeAsynchronous 
  deriving (Eq, Ord, Read, Show)

_CommandType = (Core.Name "com/azure/dtld.CommandType")

_CommandType_synchronous = (Core.Name "synchronous")

_CommandType_asynchronous = (Core.Name "asynchronous")

-- | Components enable interfaces to be composed of other interfaces. Components are different from relationships because they describe contents that are directly part of the interface. (A relationship describes a link between two interfaces.)
data Component = 
  Component {
    -- | This must be 'Component'
    componentType :: Iri,
    -- | The 'programming' name of the component. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.
    componentName :: String,
    -- | The data type of the component
    componentSchema :: Interface,
    -- | The ID of the component. If no @id is provided, the digital twin interface processor will assign one.
    componentId :: (Maybe Dtmi),
    -- | A comment for model authors
    componentComment :: (Maybe String),
    -- | A localizable description for display
    componentDescription :: (Maybe String),
    -- | A localizable name for display
    componentDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Component = (Core.Name "com/azure/dtld.Component")

_Component_type = (Core.Name "type")

_Component_name = (Core.Name "name")

_Component_schema = (Core.Name "schema")

_Component_id = (Core.Name "id")

_Component_comment = (Core.Name "comment")

_Component_description = (Core.Name "description")

_Component_displayName = (Core.Name "displayName")

-- | A digital twin model identifier
newtype Dtmi = 
  Dtmi {
    -- | A digital twin model identifier
    unDtmi :: String}
  deriving (Eq, Ord, Read, Show)

_Dtmi = (Core.Name "com/azure/dtld.Dtmi")

-- | An EnumValue describes an element of an Enum.
data EnumValue = 
  EnumValue {
    -- | The 'programming' name of the enum value. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.
    enumValueName :: String,
    -- | The on-the-wire value that maps to the EnumValue. EnumValue may be either an integer or a string and must be unique for all enum values in this enum.
    enumValueEnumValue :: IntegerOrString,
    -- | The ID of the enum value. If no @id is provided, the digital twin interface processor will assign one.
    enumValueId :: (Maybe Dtmi),
    -- | A comment for model authors
    enumValueComment :: (Maybe String),
    -- | A localizable description for display
    enumValueDescription :: (Maybe String),
    -- | A localizable name for display
    enumValueDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_EnumValue = (Core.Name "com/azure/dtld.EnumValue")

_EnumValue_name = (Core.Name "name")

_EnumValue_enumValue = (Core.Name "enumValue")

_EnumValue_id = (Core.Name "id")

_EnumValue_comment = (Core.Name "comment")

_EnumValue_description = (Core.Name "description")

_EnumValue_displayName = (Core.Name "displayName")

-- | A Field describes a field in an Object.
data Field = 
  Field {
    -- | The 'programming' name of the field. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.
    fieldName :: String,
    -- | The data type of the field
    fieldSchema :: Schema,
    -- | The ID of the field. If no @id is provided, the digital twin interface processor will assign one.
    fieldId :: (Maybe Dtmi),
    -- | A comment for model authors
    fieldComment :: (Maybe String),
    -- | A localizable description for display
    fieldDescription :: (Maybe String),
    -- | A localizable name for display
    fieldDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Field = (Core.Name "com/azure/dtld.Field")

_Field_name = (Core.Name "name")

_Field_schema = (Core.Name "schema")

_Field_id = (Core.Name "id")

_Field_comment = (Core.Name "comment")

_Field_description = (Core.Name "description")

_Field_displayName = (Core.Name "displayName")

data IntegerOrString = 
  IntegerOrStringInteger Int |
  IntegerOrStringString String
  deriving (Eq, Ord, Read, Show)

_IntegerOrString = (Core.Name "com/azure/dtld.IntegerOrString")

_IntegerOrString_integer = (Core.Name "integer")

_IntegerOrString_string = (Core.Name "string")

data Interface = 
  Interface {
    -- | A digital twin model identifier for the interface
    interfaceId :: Dtmi,
    -- | This must be 'Interface'
    interfaceType :: Iri,
    -- | The context to use when processing this interface. For this version, it must be set to 'dtmi:dtdl:context;2'
    interfaceContext :: Iri,
    -- | A comment for model authors
    interfaceComment :: (Maybe String),
    -- | A set of objects that define the contents (Telemetry, Properties, Commands, Relationships, and/or Components) of this interface
    interfaceContents :: (Maybe (Set Interface_Contents)),
    -- | A localizable description for display
    interfaceDescription :: (Maybe String),
    -- | A localizable name for display
    interfaceDisplayName :: (Maybe String),
    -- | A set of DTMIs that refer to interfaces this interface inherits from. Interfaces can inherit from multiple interfaces.
    interfaceExtends :: (Maybe (Set Interface)),
    -- | A set of IRIs or objects that refer to the reusable schemas within this interface.
    interfaceSchemas :: (Maybe (Set Schema_Interface))}
  deriving (Eq, Ord, Read, Show)

_Interface = (Core.Name "com/azure/dtld.Interface")

_Interface_id = (Core.Name "id")

_Interface_type = (Core.Name "type")

_Interface_context = (Core.Name "context")

_Interface_comment = (Core.Name "comment")

_Interface_contents = (Core.Name "contents")

_Interface_description = (Core.Name "description")

_Interface_displayName = (Core.Name "displayName")

_Interface_extends = (Core.Name "extends")

_Interface_schemas = (Core.Name "schemas")

data Interface_Contents = 
  Interface_ContentsCommand Command |
  Interface_ContentsComponent Component |
  Interface_ContentsProperty Property |
  Interface_ContentsRelationship Relationship |
  Interface_ContentsTelemetry Telemetry
  deriving (Eq, Ord, Read, Show)

_Interface_Contents = (Core.Name "com/azure/dtld.Interface.Contents")

_Interface_Contents_command = (Core.Name "command")

_Interface_Contents_component = (Core.Name "component")

_Interface_Contents_property = (Core.Name "property")

_Interface_Contents_relationship = (Core.Name "relationship")

_Interface_Contents_telemetry = (Core.Name "telemetry")

newtype Iri = 
  Iri {
    unIri :: String}
  deriving (Eq, Ord, Read, Show)

_Iri = (Core.Name "com/azure/dtld.Iri")

-- | A MapKey describes the key in a Map. The schema of a MapKey must be string.
data MapKey = 
  MapKey {
    -- | The 'programming' name of the map's key. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.
    mapKeyName :: String,
    -- | The data type of the map's key
    mapKeySchema :: Schema,
    -- | The ID of the map key. If no @id is provided, the digital twin interface processor will assign one.
    mapKeyId :: (Maybe Dtmi),
    -- | A comment for model authors
    mapKeyComment :: (Maybe String),
    -- | A localizable description for display
    mapKeyDescription :: (Maybe String),
    -- | A localizable name for display
    mapKeyDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_MapKey = (Core.Name "com/azure/dtld.MapKey")

_MapKey_name = (Core.Name "name")

_MapKey_schema = (Core.Name "schema")

_MapKey_id = (Core.Name "id")

_MapKey_comment = (Core.Name "comment")

_MapKey_description = (Core.Name "description")

_MapKey_displayName = (Core.Name "displayName")

-- | A MapValue describes the values in a Map.
data MapValue = 
  MapValue {
    -- | The 'programming' name of the map's value. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.
    mapValueName :: String,
    -- | The data type of the map's values
    mapValueSchema :: Schema,
    -- | The ID of the map value. If no @id is provided, the digital twin interface processor will assign one.
    mapValueId :: (Maybe Dtmi),
    -- | A comment for model authors
    mapValueComment :: (Maybe String),
    -- | A localizable description for display
    mapValueDescription :: (Maybe String),
    -- | A localizable name for display
    mapValueDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_MapValue = (Core.Name "com/azure/dtld.MapValue")

_MapValue_name = (Core.Name "name")

_MapValue_schema = (Core.Name "schema")

_MapValue_id = (Core.Name "id")

_MapValue_comment = (Core.Name "comment")

_MapValue_description = (Core.Name "description")

_MapValue_displayName = (Core.Name "displayName")

-- | A Property describes the read-only and read/write state of any digital twin. For example, a device serial number may be a read-only property, the desired temperature on a thermostat may be a read-write property; and the name of a room may be a read-write property.
data Property = 
  Property {
    -- | This must at least be 'Property'. It can also include a semantic type.
    propertyType :: Iri,
    -- | The 'programming' name of the property. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$..
    propertyName :: String,
    -- | The data type of the Property
    propertySchema :: Schema,
    -- | The ID of the property. If no @id is provided, the digital twin interface processor will assign one.
    propertyId :: (Maybe Dtmi),
    -- | A comment for model authors
    propertyComment :: (Maybe String),
    -- | A localizable description for display
    propertyDescription :: (Maybe String),
    -- | A localizable name for display
    propertyDisplayName :: (Maybe String),
    -- | The unit type of the property. A semantic type is required for the unit property to be available.
    propertyUnit :: (Maybe Unit),
    -- | A boolean value that indicates whether the property is writable by an external source, such as an application, or not. The default value is false (read-only).
    propertyWritable :: (Maybe Bool)}
  deriving (Eq, Ord, Read, Show)

_Property = (Core.Name "com/azure/dtld.Property")

_Property_type = (Core.Name "type")

_Property_name = (Core.Name "name")

_Property_schema = (Core.Name "schema")

_Property_id = (Core.Name "id")

_Property_comment = (Core.Name "comment")

_Property_description = (Core.Name "description")

_Property_displayName = (Core.Name "displayName")

_Property_unit = (Core.Name "unit")

_Property_writable = (Core.Name "writable")

-- | A Relationship describes a link to another digital twin and enables graphs of digital twins to be created. Relationships are different from Components because they describe a link to a separate digital twin.
data Relationship = 
  Relationship {
    -- | This must be 'Relationship'
    relationshipType :: Iri,
    -- | The 'programming' name of the relationship. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.
    relationshipName :: String,
    -- | The ID of the relationship description. If no @id is provided, the digital twin interface processor will assign one.
    relationshipId :: (Maybe Dtmi),
    -- | A comment for model authors
    relationshipComment :: (Maybe String),
    -- | A localizable description for display
    relationshipDescription :: (Maybe String),
    -- | A localizable name for display
    relationshipDisplayName :: (Maybe String),
    -- | The maximum multiplicity for the target of the relationship. The default value is infinite (there may be an unlimited number of relationship instances for this relationship).
    relationshipMaxMultiplicity :: (Maybe Int),
    -- | The minimum multiplicity for the target of the relationship. The default value is 0 (this relationship is permitted to have no instances). In DTDL v2, minMultiplicity must always be 0.
    relationshipMinMultiplicity :: (Maybe Int),
    -- | A set of Properties that define relationship-specific state
    relationshipProperties :: (Maybe (Set Property)),
    -- | An interface ID. The default value (when target is not specified) is that the target may be any interface.
    relationshipTarget :: (Maybe Interface),
    -- | A boolean value that indicates whether the relationship is writable by an external source, such as an application, or not. The default value is false (read-only).
    relationshipWritable :: (Maybe Bool)}
  deriving (Eq, Ord, Read, Show)

_Relationship = (Core.Name "com/azure/dtld.Relationship")

_Relationship_type = (Core.Name "type")

_Relationship_name = (Core.Name "name")

_Relationship_id = (Core.Name "id")

_Relationship_comment = (Core.Name "comment")

_Relationship_description = (Core.Name "description")

_Relationship_displayName = (Core.Name "displayName")

_Relationship_maxMultiplicity = (Core.Name "maxMultiplicity")

_Relationship_minMultiplicity = (Core.Name "minMultiplicity")

_Relationship_properties = (Core.Name "properties")

_Relationship_target = (Core.Name "target")

_Relationship_writable = (Core.Name "writable")

-- | Schemas are used to describe the on-the-wire or serialized format of the data in a digital twin interface. A full set of primitive data types are provided, along with support for a variety of complex schemas in the forms of Arrays, Enums, Maps, and Objects. Schemas described through digital twin's schema definition language are compatible with popular serialization formats, including JSON, Avro, and Protobuf.
data Schema = 
  SchemaPrimitive Schema_Primitive |
  SchemaComplex Schema_Complex
  deriving (Eq, Ord, Read, Show)

_Schema = (Core.Name "com/azure/dtld.Schema")

_Schema_primitive = (Core.Name "primitive")

_Schema_complex = (Core.Name "complex")

-- | An Array describes an indexable data type where each element is of the same schema. An Array elements' schema can itself be a primitive or complex schema.
data Schema_Array = 
  Schema_Array {
    -- | This must be 'Array'
    schema_ArrayType :: Iri,
    -- | The data type of the array elements
    schema_ArrayElementSchema :: Schema,
    -- | The ID of the array. If no @id is provided, the digital twin interface processor will assign one.
    schema_ArrayId :: (Maybe Dtmi),
    -- | A comment for model authors
    schema_ArrayComment :: (Maybe String),
    -- | A localizable description for display
    schema_ArrayDescription :: (Maybe String),
    -- | A localizable name for display
    schema_ArrayDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Schema_Array = (Core.Name "com/azure/dtld.Schema.Array")

_Schema_Array_type = (Core.Name "type")

_Schema_Array_elementSchema = (Core.Name "elementSchema")

_Schema_Array_id = (Core.Name "id")

_Schema_Array_comment = (Core.Name "comment")

_Schema_Array_description = (Core.Name "description")

_Schema_Array_displayName = (Core.Name "displayName")

-- | Complex schemas are designed for supporting complex data types made up of primitive data types. Currently the following complex schemas are provided: Array, Enum, Map, and Object. A complex schema can be specified directly as the value in a schema statement or described in the interface schemas set and referenced in the schema statement.
data Schema_Complex = 
  Schema_ComplexArray Schema_Array |
  Schema_ComplexEnum Schema_Enum |
  Schema_ComplexMap Schema_Map |
  Schema_ComplexObject Schema_Object
  deriving (Eq, Ord, Read, Show)

_Schema_Complex = (Core.Name "com/azure/dtld.Schema.Complex")

_Schema_Complex_array = (Core.Name "array")

_Schema_Complex_enum = (Core.Name "enum")

_Schema_Complex_map = (Core.Name "map")

_Schema_Complex_object = (Core.Name "object")

-- | An Enum describes a data type with a set of named labels that map to values. The values in an Enum can be either integers or strings, but the labels are always strings.
data Schema_Enum = 
  Schema_Enum {
    -- | Enum
    schema_EnumType :: Iri,
    -- | A set of enum value and label mappings
    schema_EnumEnumValues :: [EnumValue],
    -- | The data type for the enum values. All enum values must be of the same type.
    schema_EnumValueSchema :: IntegerOrString,
    -- | The ID of the enum. If no @id is provided, the digital twin interface processor will assign one.
    schema_EnumId :: (Maybe Dtmi),
    -- | A comment for model authors
    schema_EnumComment :: (Maybe String),
    -- | A localizable description for display
    schema_EnumDescription :: (Maybe String),
    -- | A localizable name for display
    schema_EnumDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Schema_Enum = (Core.Name "com/azure/dtld.Schema.Enum")

_Schema_Enum_type = (Core.Name "type")

_Schema_Enum_enumValues = (Core.Name "enumValues")

_Schema_Enum_valueSchema = (Core.Name "valueSchema")

_Schema_Enum_id = (Core.Name "id")

_Schema_Enum_comment = (Core.Name "comment")

_Schema_Enum_description = (Core.Name "description")

_Schema_Enum_displayName = (Core.Name "displayName")

-- | Within an interface definition, complex schemas may be defined for reusability across Telemetry, Properties, and Commands. This is designed to promote readability and improved maintenance because schemas that are reused can be defined once (per interface). Interface schemas are defined in the schemas property of an interface.
data Schema_Interface = 
  Schema_Interface {
    -- | The globally unique identifier for the schema
    schema_InterfaceId :: Dtmi,
    -- | The type of complex schema. This must refer to one of the complex schema classes (Array, Enum, Map, or Object).
    schema_InterfaceType :: Schema_Interface_Type,
    -- | A comment for model authors
    schema_InterfaceComment :: (Maybe String),
    -- | A localizable description for display
    schema_InterfaceDescription :: (Maybe String),
    -- | A localizable name for display
    schema_InterfaceDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Schema_Interface = (Core.Name "com/azure/dtld.Schema.Interface")

_Schema_Interface_id = (Core.Name "id")

_Schema_Interface_type = (Core.Name "type")

_Schema_Interface_comment = (Core.Name "comment")

_Schema_Interface_description = (Core.Name "description")

_Schema_Interface_displayName = (Core.Name "displayName")

data Schema_Interface_Type = 
  Schema_Interface_TypeArray Schema_Array |
  Schema_Interface_TypeEnum Schema_Enum |
  Schema_Interface_TypeMap Schema_Map |
  Schema_Interface_TypeObject Schema_Object
  deriving (Eq, Ord, Read, Show)

_Schema_Interface_Type = (Core.Name "com/azure/dtld.Schema.Interface.Type")

_Schema_Interface_Type_array = (Core.Name "array")

_Schema_Interface_Type_enum = (Core.Name "enum")

_Schema_Interface_Type_map = (Core.Name "map")

_Schema_Interface_Type_object = (Core.Name "object")

-- | A Map describes a data type of key-value pairs where the values share the same schema. The key in a Map must be a string. The values in a Map can be any schema.
data Schema_Map = 
  Schema_Map {
    -- | Map
    schema_MapType :: Iri,
    -- | A description of the keys in the map
    schema_MapMapKey :: MapKey,
    -- | A description of the values in the map
    schema_MapMapValue :: MapValue,
    -- | The ID of the map. If no @id is provided, the digital twin interface processor will assign one.
    schema_MapId :: (Maybe Dtmi),
    -- | A comment for model authors
    schema_MapComment :: (Maybe String),
    -- | A localizable description for display
    schema_MapDescription :: (Maybe String),
    -- | A localizable name for display
    schema_MapDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Schema_Map = (Core.Name "com/azure/dtld.Schema.Map")

_Schema_Map_type = (Core.Name "type")

_Schema_Map_mapKey = (Core.Name "mapKey")

_Schema_Map_mapValue = (Core.Name "mapValue")

_Schema_Map_id = (Core.Name "id")

_Schema_Map_comment = (Core.Name "comment")

_Schema_Map_description = (Core.Name "description")

_Schema_Map_displayName = (Core.Name "displayName")

-- | An Object describes a data type made up of named fields (like a struct in C). The fields in an Object map can be primitive or complex schemas.
data Schema_Object = 
  Schema_Object {
    -- | Object
    schema_ObjectType :: Iri,
    -- | A set of field descriptions, one for each field in the Object
    schema_ObjectFields :: (Set Field),
    -- | The ID of the object. If no @id is provided, the digital twin interface processor will assign one.
    schema_ObjectId :: (Maybe Dtmi),
    -- | A comment for model authors
    schema_ObjectComment :: (Maybe String),
    -- | A localizable description for display
    schema_ObjectDescription :: (Maybe String),
    -- | A localizable name for display
    schema_ObjectDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Schema_Object = (Core.Name "com/azure/dtld.Schema.Object")

_Schema_Object_type = (Core.Name "type")

_Schema_Object_fields = (Core.Name "fields")

_Schema_Object_id = (Core.Name "id")

_Schema_Object_comment = (Core.Name "comment")

_Schema_Object_description = (Core.Name "description")

_Schema_Object_displayName = (Core.Name "displayName")

-- | A full set of primitive data types are provided and can be specified directly as the value in a schema statement in a digital twin interface.
data Schema_Primitive = 
  -- | A boolean value
  Schema_PrimitiveBoolean  |
  -- | A full-date as defined in section 5.6 of RFC 3339
  Schema_PrimitiveDate  |
  -- | A date-time as defined in RFC 3339
  Schema_PrimitiveDateTime  |
  -- | An IEEE 8-byte floating point
  Schema_PrimitiveDouble  |
  -- | A duration in ISO 8601 format
  Schema_PrimitiveDuration  |
  -- | An IEEE 4-byte floating point
  Schema_PrimitiveFloat  |
  -- | A signed 4-byte integer
  Schema_PrimitiveInteger  |
  -- | A signed 8-byte integer
  Schema_PrimitiveLong  |
  -- | A UTF8 string
  Schema_PrimitiveString  |
  -- | A full-time as defined in section 5.6 of RFC 3339
  Schema_PrimitiveTime 
  deriving (Eq, Ord, Read, Show)

_Schema_Primitive = (Core.Name "com/azure/dtld.Schema.Primitive")

_Schema_Primitive_boolean = (Core.Name "boolean")

_Schema_Primitive_date = (Core.Name "date")

_Schema_Primitive_dateTime = (Core.Name "dateTime")

_Schema_Primitive_double = (Core.Name "double")

_Schema_Primitive_duration = (Core.Name "duration")

_Schema_Primitive_float = (Core.Name "float")

_Schema_Primitive_integer = (Core.Name "integer")

_Schema_Primitive_long = (Core.Name "long")

_Schema_Primitive_string = (Core.Name "string")

_Schema_Primitive_time = (Core.Name "time")

-- | Telemetry describes the data emitted by any digital twin, whether the data is a regular stream of sensor readings or a computed stream of data, such as occupancy, or an occasional error or information message.
data Telemetry = 
  Telemetry {
    -- | This must be at least 'Telemetry'. It can also include a semantic type
    telemetryType :: Iri,
    -- | The 'programming' name of the telemetry. The name may only contain the characters a-z, A-Z, 0-9, and underscore, and must match this regular expression ^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$..
    telemetryName :: String,
    -- | The data type of the Telemetry
    telemetrySchema :: Schema,
    -- | The ID of the telemetry. If no @id is provided, the digital twin interface processor will assign one.
    telemetryId :: (Maybe Dtmi),
    -- | A comment for model authors
    telemetryComment :: (Maybe String),
    -- | A localizable description for display
    telemetryDescription :: (Maybe String),
    -- | A localizable name for display
    telemetryDisplayName :: (Maybe String),
    -- | The unit type of the Telemetry. A semantic type is required for the unit property to be available.
    telemetryUnit :: (Maybe Unit)}
  deriving (Eq, Ord, Read, Show)

_Telemetry = (Core.Name "com/azure/dtld.Telemetry")

_Telemetry_type = (Core.Name "type")

_Telemetry_name = (Core.Name "name")

_Telemetry_schema = (Core.Name "schema")

_Telemetry_id = (Core.Name "id")

_Telemetry_comment = (Core.Name "comment")

_Telemetry_description = (Core.Name "description")

_Telemetry_displayName = (Core.Name "displayName")

_Telemetry_unit = (Core.Name "unit")

data Unit = 
  Unit {}
  deriving (Eq, Ord, Read, Show)

_Unit = (Core.Name "com/azure/dtld.Unit")
