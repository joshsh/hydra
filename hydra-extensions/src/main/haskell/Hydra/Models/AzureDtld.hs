module Hydra.Models.AzureDtld (dtldModule) where

import Hydra.Dsl.Types as Types
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Annotations
import Hydra.Sources.Tier4.All


dtmi128 :: Type
dtmi128 = bounded Nothing (Just 128) $ dtld "Dtmi"

dtmi2048 :: Type
dtmi2048 = bounded Nothing (Just 2048) $ dtld "Dtmi"

idField :: Bool -> Int -> String -> FieldType
idField req maxlen desc = "id">: doc desc $ if req then t else optional t
  where
    t = bounded Nothing (Just maxlen) $ dtld "Dtmi"

idOptionalField :: [Char] -> FieldType
idOptionalField cat = idField False 2048 $
  "The ID of the " ++ cat ++ ". If no @id is provided, the digital twin interface processor will assign one."

nonemptyString64 :: Type
nonemptyString64 = boundedString (Just 1) (Just 64)

nonemptyString512 :: Type
nonemptyString512 = boundedString (Just 1) (Just 512)

string128 :: Type
string128 = boundedString Nothing (Just 128)

commentField :: FieldType
commentField = "comment">: doc "A comment for model authors" $ optional nonemptyString512

descriptionField :: FieldType
descriptionField = "description">: doc "A localizable description for display" $ optional nonemptyString512

displayNameField :: FieldType
displayNameField = "displayName">: doc "A localizable name for display" $ optional nonemptyString64

nameField :: String -> String -> FieldType
nameField cat regex = "name">: doc (
  "The 'programming' name of the " ++ cat ++ ". The name may only contain the characters " ++
  "a-z, A-Z, 0-9, and underscore, and must match this regular expression " ++ regex ++ ".")
  nonemptyString64

schemaField :: String -> FieldType
schemaField cat = "schema">: doc ("The data type of the " ++ cat) $ dtld "Schema"

schemaInterfaceField :: String -> FieldType
schemaInterfaceField cat = "schema">: doc ("The data type of the " ++ cat) $ dtld "Interface"

typeField :: String -> FieldType
typeField desc = "type">: doc desc $ dtld "Iri"

unitField :: String -> FieldType
unitField cat = "unit">:
  doc ("The unit type of the " ++ cat ++ ". A semantic type is required for the unit property to be available.") $
  optional $ dtld "Unit"

writableField :: String -> FieldType
writableField cat = "writable">:
  doc (
    "A boolean value that indicates whether the " ++ cat ++ " is writable by an external source, " ++
    "such as an application, or not. The default value is false (read-only).") $
  optional boolean

dtld :: String -> Type
dtld = typeref dtldNs

dtldNs :: Namespace
dtldNs = Namespace "com/azure/dtld"

dtldModule :: Module
dtldModule = Module dtldNs elements [hydraCoreModule] $
    Just ("An Azure Digital Twin Definition Language (DTLD) model. Based on:\n" ++
      "  https://github.com/Azure/opendigitaltwins-dtdl/blob/master/DTDL/v2/dtdlv2.md#digital-twins-definition-language\n" ++
      "DTLD features which are not currently included in this model:\n" ++
      "  * geospatial schemas (https://github.com/Azure/opendigitaltwins-dtdl/blob/master/DTDL/v2/dtdlv2.md#geospatial-schemas)\n" ++
      "  * semantic types and units (https://github.com/Azure/opendigitaltwins-dtdl/blob/master/DTDL/v2/dtdlv2.md#semantic-types)\n" ++
      "  * model versioning (https://github.com/Azure/opendigitaltwins-dtdl/blob/master/DTDL/v2/dtdlv2.md#model-versioning)")
  where
    def = datatype dtldNs

    elements = [
      def "Command" $
        doc "A Command describes a function or operation that can be performed on any digital twin." $
        record [
          typeField "This must be 'Command'",
          nameField "command" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$",
          idOptionalField "command",
          commentField,
          descriptionField,
          displayNameField,
          "commandType">:
            doc (
              "This property is deprecated. Either value, synchronous or asynchronous, has the same meaning: " ++
              "a command that starts execution within a configurable time and that completes execution " ++
              "within a configurable time.") $
            optional $ dtld "CommandType",
          "request">:
            doc "A description of the input to the Command" $
            optional $ dtld "CommandPayload",
          "response">:
            doc "A description of the output of the Command" $
            optional $ dtld "CommandPayload"],

      def "CommandPayload" $
        doc "A CommandPayload describes the inputs to or the outputs from a Command." $
        record [
          nameField "payload" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$",
          schemaField "payload",
          idOptionalField "payload",
          commentField,
          descriptionField,
          displayNameField],

      def "CommandType" $
        doc (
          "CommandType is deprecated. Either value, synchronous or asynchronous, has the same meaning: " ++
          "a command that starts execution within a configurable time and that completes execution " ++
          "within a configurable time.") $
        enum [
          "synchronous",
          "asynchronous"],

      def "Component" $
        doc (
          "Components enable interfaces to be composed of other interfaces. Components are different from " ++
          "relationships because they describe contents that are directly part of the interface. " ++
          "(A relationship describes a link between two interfaces.)") $
        record [
          typeField "This must be 'Component'",
          nameField "component" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$",
          schemaInterfaceField "component", -- Note: "maximum depth of 1; no cycles"
          idOptionalField "component",
          commentField,
          descriptionField,
          displayNameField],

      def "Dtmi" $
        doc "A digital twin model identifier" string,

      def "EnumValue" $
        doc "An EnumValue describes an element of an Enum." $
        record [
          nameField "enum value" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$",
          "enumValue">:
            doc (
              "The on-the-wire value that maps to the EnumValue. EnumValue may be either an integer or a string " ++
              "and must be unique for all enum values in this enum.") $
            dtld "IntegerOrString",
          idOptionalField "enum value",
          commentField,
          descriptionField,
          displayNameField],

      def "Field" $
        doc "A Field describes a field in an Object." $
        record [
          nameField "field" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$",
          schemaField "field",
          idOptionalField "field",
          commentField,
          descriptionField,
          displayNameField],

      def "IntegerOrString" $ union [
        "integer">: int32,
        "string">: string],

      def "Interface" $ record [
        idField True 128 "A digital twin model identifier for the interface",
        typeField "This must be 'Interface'",
        "context">:
          doc (
            "The context to use when processing this interface. " ++
            "For this version, it must be set to 'dtmi:dtdl:context;2'") $
          dtld "Iri",
        commentField,
        "contents">:
          doc (
            "A set of objects that define the contents (Telemetry, Properties, Commands, Relationships, " ++
            "and/or Components) of this interface") $
          optional $ boundedSet Nothing (Just 300) $ dtld "Interface.Contents",
        descriptionField,
        displayNameField,
        "extends">: -- Note: there is a maximum depth of 10 levels, not captured here
          doc (
            "A set of DTMIs that refer to interfaces this interface inherits from. " ++
            "Interfaces can inherit from multiple interfaces.") $
          optional $ boundedSet Nothing (Just 2) $ dtld "Interface",
        "schemas">:
          doc "A set of IRIs or objects that refer to the reusable schemas within this interface." $
          optional $ set $ dtld "Schema.Interface"],

      def "Interface.Contents" $ union [
        "command">: dtld "Command",
        "component">: dtld "Component",
        "property">: dtld "Property",
        "relationship">: dtld "Relationship",
        "telemetry">: dtld "Telemetry"],

      def "Iri" string,

--      -- Note: this is a helper type; not explicitly definde in DTLD
--      def "IriOrSchema.Interface" $ union [
--        "iri">: dtld "Iri",
--        "interfaceSchema">: dtld "Schema.Interface"],

      def "MapKey" $
        doc "A MapKey describes the key in a Map. The schema of a MapKey must be string." $
        record [
          nameField "map's key" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$",
          schemaField "map's key", -- Note: "must be string"
          idOptionalField "map key",
          commentField,
          descriptionField,
          displayNameField],

      def "MapValue" $
        doc "A MapValue describes the values in a Map." $
        record [
          nameField "map's value" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$",
          schemaField "map's values",
          idOptionalField "map value",
          commentField,
          descriptionField,
          displayNameField],

      def "Property" $
        doc (
          "A Property describes the read-only and read/write state of any digital twin. " ++
          "For example, a device serial number may be a read-only property, the desired temperature " ++
          "on a thermostat may be a read-write property; and the name of a room may be a read-write property.") $
        record [
          typeField "This must at least be 'Property'. It can also include a semantic type.",
          nameField "property" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.",
          -- Note: "may not be Array nor any complex schema that contains Array"
          schemaField "Property",
          idOptionalField "property",
          commentField,
          descriptionField,
          displayNameField,
          unitField "property",
          writableField "property"],

      def "Relationship" $
        doc (
          "A Relationship describes a link to another digital twin and enables graphs of digital twins " ++
          "to be created. Relationships are different from Components because they describe a link " ++
          "to a separate digital twin.") $
        record [
          typeField "This must be 'Relationship'",
          nameField "relationship" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$",
          idOptionalField "relationship description",
          commentField,
          descriptionField,
          displayNameField,
          "maxMultiplicity">:
            -- Note: "must be >= 1 and >= minMultiplicity"
            doc (
              "The maximum multiplicity for the target of the relationship. The default value is infinite " ++
              "(there may be an unlimited number of relationship instances for this relationship).") $
            optional $ bounded (Just 1) Nothing int32,
          "minMultiplicity">:
            -- Note: "must be <= maxMultiplicity"
            doc (
              "The minimum multiplicity for the target of the relationship. The default value is 0 " ++
              "(this relationship is permitted to have no instances). In DTDL v2, minMultiplicity must always be 0.") $
            optional $ bounded (Just 0) Nothing int32,
          "properties">:
            doc "A set of Properties that define relationship-specific state" $
            optional $ bounded Nothing (Just 300) $ set $ dtld "Property",
          "target">:
            doc "An interface ID. The default value (when target is not specified) is that the target may be any interface." $
            optional $ dtld "Interface",
            writableField "relationship"],

      def "Schema" $
        doc (
          "Schemas are used to describe the on-the-wire or serialized format of the data in a digital twin interface. " ++
          "A full set of primitive data types are provided, along with support for a variety of complex schemas " ++
          "in the forms of Arrays, Enums, Maps, and Objects. Schemas described through digital twin's schema " ++
          "definition language are compatible with popular serialization formats, including JSON, Avro, and Protobuf.") $
        union [
          "primitive">: dtld "Schema.Primitive",
          "complex">: dtld "Schema.Complex"],

      def "Schema.Array" $
        doc (
          "An Array describes an indexable data type where each element is of the same schema. " ++
          "An Array elements' schema can itself be a primitive or complex schema.") $
        record [
          typeField "This must be 'Array'",
          "elementSchema">:
            doc "The data type of the array elements" $
            dtld "Schema",
          idOptionalField "array",
          commentField,
          descriptionField,
          displayNameField],

      def "Schema.Complex" $
        doc ("Complex schemas are designed for supporting complex data types made up of primitive data types. " ++
             "Currently the following complex schemas are provided: Array, Enum, Map, and Object. " ++
             "A complex schema can be specified directly as the value in a schema statement or " ++
             "described in the interface schemas set and referenced in the schema statement.") $
        union [
          -- Note: interface schemas are currently special, and are not included in this union
          "array">: dtld "Schema.Array",
          "enum">: dtld "Schema.Enum",
          "map">: dtld "Schema.Map",
          "object">: dtld "Schema.Object"],

      def "Schema.Enum" $
        doc (
          "An Enum describes a data type with a set of named labels that map to values. The values in an Enum " ++
          "can be either integers or strings, but the labels are always strings.") $
        record [
          typeField "Enum",
          "enumValues">:
            doc "A set of enum value and label mappings" $
            list $ dtld "EnumValue", -- Note: the spec seems to be wrong here; it specifies a lone "EnumValue" instead of a set
          "valueSchema">:
            doc "The data type for the enum values. All enum values must be of the same type." $
            dtld "IntegerOrString",
          idOptionalField "enum",
          commentField,
          descriptionField,
          displayNameField],

      def "Schema.Interface" $
        doc (
          "Within an interface definition, complex schemas may be defined for reusability across " ++
          "Telemetry, Properties, and Commands. This is designed to promote readability and improved " ++
          "maintenance because schemas that are reused can be defined once (per interface). Interface schemas " ++
          "are defined in the schemas property of an interface.") $
        record [
          idField True 2048 "The globally unique identifier for the schema",
          "type">:
            doc "The type of complex schema. This must refer to one of the complex schema classes (Array, Enum, Map, or Object)." $
            dtld "Schema.Interface.Type",
          commentField,
          descriptionField,
          displayNameField],

      def "Schema.Interface.Type" $ union [
        "array">: dtld "Schema.Array",
        "enum">: dtld "Schema.Enum",
        "map">: dtld "Schema.Map",
        "object">: dtld "Schema.Object"],

      def "Schema.Map" $
        doc ("A Map describes a data type of key-value pairs where the values share the same schema. " ++
             "The key in a Map must be a string. The values in a Map can be any schema.") $
        record [
          typeField "Map",
          "mapKey">:
            doc "A description of the keys in the map" $
            dtld "MapKey",
          "mapValue">:
            doc "A description of the values in the map" $
            dtld "MapValue",
          idOptionalField "map",
          commentField,
          descriptionField,
          displayNameField],

      def "Schema.Object" $
        doc (
          "An Object describes a data type made up of named fields (like a struct in C). " ++
          "The fields in an Object map can be primitive or complex schemas.") $
        record [
          typeField "Object",
          "fields">:
            doc "A set of field descriptions, one for each field in the Object" $
            bounded Nothing (Just 30) $ set $ dtld "Field", -- Note: "max depth 5 levels"
          idOptionalField "object",
          commentField,
          descriptionField,
          displayNameField],

      def "Schema.Primitive" $
        doc (
          "A full set of primitive data types are provided and can be specified directly as the value " ++
          "in a schema statement in a digital twin interface.") $
        union [
          "boolean">: doc "A boolean value" unit,
          "date">: doc "A full-date as defined in section 5.6 of RFC 3339" unit,
          "dateTime">: doc "A date-time as defined in RFC 3339" unit,
          "double">: doc "An IEEE 8-byte floating point" unit,
          "duration">: doc "A duration in ISO 8601 format" unit,
          "float">: doc "An IEEE 4-byte floating point" unit,
          "integer">: doc "A signed 4-byte integer" unit,
          "long">: doc "A signed 8-byte integer" unit,
          "string">: doc "A UTF8 string" unit,
          "time">: doc "A full-time as defined in section 5.6 of RFC 3339" unit],

      def "Telemetry" $
        doc (
          "Telemetry describes the data emitted by any digital twin, whether the data is a regular stream " ++
          "of sensor readings or a computed stream of data, such as occupancy, " ++
          "or an occasional error or information message.") $
        record [
          typeField "This must be at least 'Telemetry'. It can also include a semantic type",
          nameField "telemetry" "^[a-zA-Z](?:[a-zA-Z0-9_]*[a-zA-Z0-9])?$.",
          schemaField "Telemetry",
          idField False 2048
            "The ID of the telemetry. If no @id is provided, the digital twin interface processor will assign one.",
          commentField,
          descriptionField,
          displayNameField,
          unitField "Telemetry"],

      def "Unit" unit]
