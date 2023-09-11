-- | A model for PDL (Pegasus Data Language) schemas. Based on the specification at:
-- |   https://linkedin.github.io/rest.li/pdl_schema

module Hydra.Langs.Pegasus.Pdl where

import qualified Hydra.Core as Core
import qualified Hydra.Json as Json
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | Annotations which can be applied to record fields, aliased union members, enum symbols, or named schemas
data Annotations = 
  Annotations {
    annotationsDoc :: (Maybe String),
    annotationsDeprecated :: Bool}
  deriving (Eq, Ord, Read, Show)

_Annotations = (Core.Name "hydra/langs/pegasus/pdl.Annotations")

_Annotations_doc = (Core.FieldName "doc")

_Annotations_deprecated = (Core.FieldName "deprecated")

data EnumField = 
  EnumField {
    enumFieldName :: EnumFieldName,
    enumFieldAnnotations :: Annotations}
  deriving (Eq, Ord, Read, Show)

_EnumField = (Core.Name "hydra/langs/pegasus/pdl.EnumField")

_EnumField_name = (Core.FieldName "name")

_EnumField_annotations = (Core.FieldName "annotations")

newtype EnumFieldName = 
  EnumFieldName {
    unEnumFieldName :: String}
  deriving (Eq, Ord, Read, Show)

_EnumFieldName = (Core.Name "hydra/langs/pegasus/pdl.EnumFieldName")

data EnumSchema = 
  EnumSchema {
    enumSchemaFields :: [EnumField]}
  deriving (Eq, Ord, Read, Show)

_EnumSchema = (Core.Name "hydra/langs/pegasus/pdl.EnumSchema")

_EnumSchema_fields = (Core.FieldName "fields")

newtype FieldName = 
  FieldName {
    unFieldName :: String}
  deriving (Eq, Ord, Read, Show)

_FieldName = (Core.Name "hydra/langs/pegasus/pdl.FieldName")

data NamedSchema = 
  NamedSchema {
    namedSchemaQualifiedName :: QualifiedName,
    namedSchemaType :: NamedSchema_Type,
    namedSchemaAnnotations :: Annotations}
  deriving (Eq, Ord, Read, Show)

_NamedSchema = (Core.Name "hydra/langs/pegasus/pdl.NamedSchema")

_NamedSchema_qualifiedName = (Core.FieldName "qualifiedName")

_NamedSchema_type = (Core.FieldName "type")

_NamedSchema_annotations = (Core.FieldName "annotations")

data NamedSchema_Type = 
  NamedSchema_TypeRecord RecordSchema |
  NamedSchema_TypeEnum EnumSchema |
  NamedSchema_TypeTyperef Schema
  deriving (Eq, Ord, Read, Show)

_NamedSchema_Type = (Core.Name "hydra/langs/pegasus/pdl.NamedSchema.Type")

_NamedSchema_Type_record = (Core.FieldName "record")

_NamedSchema_Type_enum = (Core.FieldName "enum")

_NamedSchema_Type_typeref = (Core.FieldName "typeref")

newtype Name = 
  Name {
    unName :: String}
  deriving (Eq, Ord, Read, Show)

_Name = (Core.Name "hydra/langs/pegasus/pdl.Name")

newtype Namespace = 
  Namespace {
    unNamespace :: String}
  deriving (Eq, Ord, Read, Show)

_Namespace = (Core.Name "hydra/langs/pegasus/pdl.Namespace")

newtype Package = 
  Package {
    unPackage :: String}
  deriving (Eq, Ord, Read, Show)

_Package = (Core.Name "hydra/langs/pegasus/pdl.Package")

data PrimitiveType = 
  PrimitiveTypeBoolean  |
  PrimitiveTypeBytes  |
  PrimitiveTypeDouble  |
  PrimitiveTypeFloat  |
  PrimitiveTypeInt  |
  PrimitiveTypeLong  |
  PrimitiveTypeString 
  deriving (Eq, Ord, Read, Show)

_PrimitiveType = (Core.Name "hydra/langs/pegasus/pdl.PrimitiveType")

_PrimitiveType_boolean = (Core.FieldName "boolean")

_PrimitiveType_bytes = (Core.FieldName "bytes")

_PrimitiveType_double = (Core.FieldName "double")

_PrimitiveType_float = (Core.FieldName "float")

_PrimitiveType_int = (Core.FieldName "int")

_PrimitiveType_long = (Core.FieldName "long")

_PrimitiveType_string = (Core.FieldName "string")

newtype PropertyKey = 
  PropertyKey {
    unPropertyKey :: String}
  deriving (Eq, Ord, Read, Show)

_PropertyKey = (Core.Name "hydra/langs/pegasus/pdl.PropertyKey")

data Property = 
  Property {
    propertyKey :: PropertyKey,
    propertyValue :: (Maybe Json.Value)}
  deriving (Eq, Ord, Read, Show)

_Property = (Core.Name "hydra/langs/pegasus/pdl.Property")

_Property_key = (Core.FieldName "key")

_Property_value = (Core.FieldName "value")

data QualifiedName = 
  QualifiedName {
    qualifiedNameName :: Name,
    qualifiedNameNamespace :: (Maybe Namespace)}
  deriving (Eq, Ord, Read, Show)

_QualifiedName = (Core.Name "hydra/langs/pegasus/pdl.QualifiedName")

_QualifiedName_name = (Core.FieldName "name")

_QualifiedName_namespace = (Core.FieldName "namespace")

data RecordField = 
  RecordField {
    recordFieldName :: FieldName,
    recordFieldValue :: Schema,
    recordFieldOptional :: Bool,
    recordFieldDefault :: (Maybe Json.Value),
    recordFieldAnnotations :: Annotations}
  deriving (Eq, Ord, Read, Show)

_RecordField = (Core.Name "hydra/langs/pegasus/pdl.RecordField")

_RecordField_name = (Core.FieldName "name")

_RecordField_value = (Core.FieldName "value")

_RecordField_optional = (Core.FieldName "optional")

_RecordField_default = (Core.FieldName "default")

_RecordField_annotations = (Core.FieldName "annotations")

data RecordSchema = 
  RecordSchema {
    recordSchemaFields :: [RecordField],
    recordSchemaIncludes :: [NamedSchema]}
  deriving (Eq, Ord, Read, Show)

_RecordSchema = (Core.Name "hydra/langs/pegasus/pdl.RecordSchema")

_RecordSchema_fields = (Core.FieldName "fields")

_RecordSchema_includes = (Core.FieldName "includes")

data Schema = 
  SchemaArray Schema |
  SchemaFixed Int |
  SchemaInline NamedSchema |
  SchemaMap Schema |
  SchemaNamed QualifiedName |
  SchemaNull  |
  SchemaPrimitive PrimitiveType |
  SchemaUnion UnionSchema
  deriving (Eq, Ord, Read, Show)

_Schema = (Core.Name "hydra/langs/pegasus/pdl.Schema")

_Schema_array = (Core.FieldName "array")

_Schema_fixed = (Core.FieldName "fixed")

_Schema_inline = (Core.FieldName "inline")

_Schema_map = (Core.FieldName "map")

_Schema_named = (Core.FieldName "named")

_Schema_null = (Core.FieldName "null")

_Schema_primitive = (Core.FieldName "primitive")

_Schema_union = (Core.FieldName "union")

data SchemaFile = 
  SchemaFile {
    schemaFileNamespace :: Namespace,
    schemaFilePackage :: (Maybe Package),
    schemaFileImports :: [QualifiedName],
    schemaFileSchemas :: [NamedSchema]}
  deriving (Eq, Ord, Read, Show)

_SchemaFile = (Core.Name "hydra/langs/pegasus/pdl.SchemaFile")

_SchemaFile_namespace = (Core.FieldName "namespace")

_SchemaFile_package = (Core.FieldName "package")

_SchemaFile_imports = (Core.FieldName "imports")

_SchemaFile_schemas = (Core.FieldName "schemas")

data UnionMember = 
  UnionMember {
    unionMemberAlias :: (Maybe FieldName),
    unionMemberValue :: Schema,
    unionMemberAnnotations :: Annotations}
  deriving (Eq, Ord, Read, Show)

_UnionMember = (Core.Name "hydra/langs/pegasus/pdl.UnionMember")

_UnionMember_alias = (Core.FieldName "alias")

_UnionMember_value = (Core.FieldName "value")

_UnionMember_annotations = (Core.FieldName "annotations")

newtype UnionSchema = 
  UnionSchema {
    unUnionSchema :: [UnionMember]}
  deriving (Eq, Ord, Read, Show)

_UnionSchema = (Core.Name "hydra/langs/pegasus/pdl.UnionSchema")