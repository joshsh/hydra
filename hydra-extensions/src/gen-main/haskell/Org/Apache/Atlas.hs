-- | The Apache Atlas meta-model
-- | Based on the the org.apache.atlas.model package in the master branch as of 2022-06-01
-- |   https://github.com/apache/atlas/tree/master/intg/src/main/java/org/apache/atlas/model

module Org.Apache.Atlas where

import qualified Hydra.Core as Core
import qualified Hydra.Langs.Xml.Schema as Schema
import Data.List
import Data.Map
import Data.Set

-- | class that captures details of a struct-attribute.
data AtlasAttributeDef = 
  AtlasAttributeDef {
    atlasAttributeDefName :: (Maybe String),
    atlasAttributeDefTypeName :: (Maybe String),
    atlasAttributeDefIsOptional :: Bool,
    atlasAttributeDefCardinality :: (Maybe AtlasAttributeDef_Cardinality),
    atlasAttributeDefValuesMinCount :: Int,
    atlasAttributeDefValuesMaxCount :: Int,
    atlasAttributeDefIsUnique :: Bool,
    atlasAttributeDefIsIndexable :: Bool,
    atlasAttributeDefIncludeInNotification :: Bool,
    atlasAttributeDefDefaultValue :: (Maybe String),
    atlasAttributeDefDescription :: (Maybe String),
    atlasAttributeDefSearchWeight :: Int,
    atlasAttributeDefIndexType :: (Maybe AtlasAttributeDef_IndexType),
    atlasAttributeDefConstraints :: [AtlasConstraintDef],
    atlasAttributeDefOptions :: (Map String String),
    atlasAttributeDefDisplayName :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_AtlasAttributeDef = (Core.Name "org/apache/atlas.AtlasAttributeDef")

_AtlasAttributeDef_name = (Core.Name "name")

_AtlasAttributeDef_typeName = (Core.Name "typeName")

_AtlasAttributeDef_isOptional = (Core.Name "isOptional")

_AtlasAttributeDef_cardinality = (Core.Name "cardinality")

_AtlasAttributeDef_valuesMinCount = (Core.Name "valuesMinCount")

_AtlasAttributeDef_valuesMaxCount = (Core.Name "valuesMaxCount")

_AtlasAttributeDef_isUnique = (Core.Name "isUnique")

_AtlasAttributeDef_isIndexable = (Core.Name "isIndexable")

_AtlasAttributeDef_includeInNotification = (Core.Name "includeInNotification")

_AtlasAttributeDef_defaultValue = (Core.Name "defaultValue")

_AtlasAttributeDef_description = (Core.Name "description")

_AtlasAttributeDef_searchWeight = (Core.Name "searchWeight")

_AtlasAttributeDef_indexType = (Core.Name "indexType")

_AtlasAttributeDef_constraints = (Core.Name "constraints")

_AtlasAttributeDef_options = (Core.Name "options")

_AtlasAttributeDef_displayName = (Core.Name "displayName")

data AtlasAttributeDef_Cardinality = 
  AtlasAttributeDef_CardinalitySingle  |
  AtlasAttributeDef_CardinalityList  |
  AtlasAttributeDef_CardinalitySet 
  deriving (Eq, Ord, Read, Show)

_AtlasAttributeDef_Cardinality = (Core.Name "org/apache/atlas.AtlasAttributeDef.Cardinality")

_AtlasAttributeDef_Cardinality_single = (Core.Name "single")

_AtlasAttributeDef_Cardinality_list = (Core.Name "list")

_AtlasAttributeDef_Cardinality_set = (Core.Name "set")

data AtlasAttributeDef_IndexType = 
  AtlasAttributeDef_IndexTypeDefault  |
  AtlasAttributeDef_IndexTypeString 
  deriving (Eq, Ord, Read, Show)

_AtlasAttributeDef_IndexType = (Core.Name "org/apache/atlas.AtlasAttributeDef.IndexType")

_AtlasAttributeDef_IndexType_default = (Core.Name "default")

_AtlasAttributeDef_IndexType_string = (Core.Name "string")

-- | Base class that captures common-attributes for all Atlas types.
data AtlasBaseTypeDef = 
  AtlasBaseTypeDef {
    atlasBaseTypeDefCategory :: (Maybe TypeCategory),
    atlasBaseTypeDefGuid :: (Maybe String),
    atlasBaseTypeDefCreatedBy :: (Maybe String),
    atlasBaseTypeDefUpdatedBy :: (Maybe String),
    atlasBaseTypeDefCreateTime :: (Maybe Schema.DateTime),
    atlasBaseTypeDefUpdateTime :: (Maybe Schema.DateTime),
    atlasBaseTypeDefVersion :: (Maybe Integer),
    atlasBaseTypeDefName :: (Maybe String),
    atlasBaseTypeDefDescription :: (Maybe String),
    atlasBaseTypeDefTypeVersion :: (Maybe String),
    atlasBaseTypeDefServiceType :: (Maybe String),
    atlasBaseTypeDefOptions :: (Map String String)}
  deriving (Eq, Ord, Read, Show)

_AtlasBaseTypeDef = (Core.Name "org/apache/atlas.AtlasBaseTypeDef")

_AtlasBaseTypeDef_category = (Core.Name "category")

_AtlasBaseTypeDef_guid = (Core.Name "guid")

_AtlasBaseTypeDef_createdBy = (Core.Name "createdBy")

_AtlasBaseTypeDef_updatedBy = (Core.Name "updatedBy")

_AtlasBaseTypeDef_createTime = (Core.Name "createTime")

_AtlasBaseTypeDef_updateTime = (Core.Name "updateTime")

_AtlasBaseTypeDef_version = (Core.Name "version")

_AtlasBaseTypeDef_name = (Core.Name "name")

_AtlasBaseTypeDef_description = (Core.Name "description")

_AtlasBaseTypeDef_typeVersion = (Core.Name "typeVersion")

_AtlasBaseTypeDef_serviceType = (Core.Name "serviceType")

_AtlasBaseTypeDef_options = (Core.Name "options")

-- | class that captures details of a constraint.
data AtlasConstraintDef = 
  AtlasConstraintDef {
    atlasConstraintDefType :: (Maybe String),
    atlasConstraintDefParams :: (Map String String)}
  deriving (Eq, Ord, Read, Show)

_AtlasConstraintDef = (Core.Name "org/apache/atlas.AtlasConstraintDef")

_AtlasConstraintDef_type = (Core.Name "type")

_AtlasConstraintDef_params = (Core.Name "params")

-- | class that captures details of a entity-type.
data AtlasEntityDef = 
  AtlasEntityDef {
    atlasEntityDefAsAtlasStructDef :: AtlasStructDef,
    atlasEntityDefSuperTypes :: (Set String),
    -- | the value of this field is derived from 'superTypes' specified in all AtlasEntityDef
    atlasEntityDefSubTypes :: (Set String),
    -- | the value of this field is derived from all the relationshipDefs this entityType is referenced in
    atlasEntityDefRelationshipAttributeDefs :: [AtlasRelationshipAttributeDef],
    -- | the value of this field is derived from all the businessMetadataDefs this entityType is referenced in
    atlasEntityDefBusinessAttributeDefs :: (Map String [AtlasAttributeDef])}
  deriving (Eq, Ord, Read, Show)

_AtlasEntityDef = (Core.Name "org/apache/atlas.AtlasEntityDef")

_AtlasEntityDef_asAtlasStructDef = (Core.Name "asAtlasStructDef")

_AtlasEntityDef_superTypes = (Core.Name "superTypes")

_AtlasEntityDef_subTypes = (Core.Name "subTypes")

_AtlasEntityDef_relationshipAttributeDefs = (Core.Name "relationshipAttributeDefs")

_AtlasEntityDef_businessAttributeDefs = (Core.Name "businessAttributeDefs")

-- | class that captures details of a struct-attribute.
data AtlasRelationshipAttributeDef = 
  AtlasRelationshipAttributeDef {
    atlasRelationshipAttributeDefAsAtlasAttributeDef :: AtlasAttributeDef,
    atlasRelationshipAttributeDefRelationshipTypeName :: (Maybe String),
    atlasRelationshipAttributeDefIsLegacyAttribute :: Bool}
  deriving (Eq, Ord, Read, Show)

_AtlasRelationshipAttributeDef = (Core.Name "org/apache/atlas.AtlasRelationshipAttributeDef")

_AtlasRelationshipAttributeDef_asAtlasAttributeDef = (Core.Name "asAtlasAttributeDef")

_AtlasRelationshipAttributeDef_relationshipTypeName = (Core.Name "relationshipTypeName")

_AtlasRelationshipAttributeDef_isLegacyAttribute = (Core.Name "isLegacyAttribute")

-- | class that captures details of a struct-type.
data AtlasStructDef = 
  AtlasStructDef {
    atlasStructDefAsAtlasBaseTypeDef :: AtlasBaseTypeDef,
    atlasStructDefAttributeDefs :: [AtlasAttributeDef]}
  deriving (Eq, Ord, Read, Show)

_AtlasStructDef = (Core.Name "org/apache/atlas.AtlasStructDef")

_AtlasStructDef_asAtlasBaseTypeDef = (Core.Name "asAtlasBaseTypeDef")

_AtlasStructDef_attributeDefs = (Core.Name "attributeDefs")

data TypeCategory = 
  TypeCategoryPrimitive  |
  TypeCategoryObjectIdType  |
  TypeCategoryEnum  |
  TypeCategoryStruct  |
  TypeCategoryClassification  |
  TypeCategoryEntity  |
  TypeCategoryArray  |
  TypeCategoryMap  |
  TypeCategoryRelationship  |
  TypeCategoryBusinessMetadata 
  deriving (Eq, Ord, Read, Show)

_TypeCategory = (Core.Name "org/apache/atlas.TypeCategory")

_TypeCategory_primitive = (Core.Name "primitive")

_TypeCategory_objectIdType = (Core.Name "objectIdType")

_TypeCategory_enum = (Core.Name "enum")

_TypeCategory_struct = (Core.Name "struct")

_TypeCategory_classification = (Core.Name "classification")

_TypeCategory_entity = (Core.Name "entity")

_TypeCategory_array = (Core.Name "array")

_TypeCategory_map = (Core.Name "map")

_TypeCategory_relationship = (Core.Name "relationship")

_TypeCategory_businessMetadata = (Core.Name "businessMetadata")
