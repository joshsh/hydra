-- | An interpretation of Codd's Relational Model, as described in 'A Relational Model of Data for Large Shared Data Banks' (1970). Types ('domains') and values are parameterized so as to allow for application-specific implementations. No special support is provided for 'nonsimple' domains; i.e. relations are assumed to be normalized.

module Hydra.Langs.RelationalModel where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | A name for a domain which serves to identify the role played by that domain in the given relation; a 'role name' in Codd
newtype ColumnName = 
  ColumnName {
    -- | A name for a domain which serves to identify the role played by that domain in the given relation; a 'role name' in Codd
    unColumnName :: String}
  deriving (Eq, Ord, Read, Show)

_ColumnName = (Core.Name "hydra/langs/relationalModel.ColumnName")

-- | An abstract specification of the domain represented by a column in a relation; a role
data ColumnSchema t = 
  ColumnSchema {
    -- | A unique name for the column
    columnSchemaName :: ColumnName,
    -- | The domain (type) of the column
    columnSchemaDomain :: t,
    -- | Whether this column represents the primary key of its relation
    columnSchemaIsPrimaryKey :: Bool}
  deriving (Eq, Ord, Read, Show)

_ColumnSchema = (Core.Name "hydra/langs/relationalModel.ColumnSchema")

_ColumnSchema_name = (Core.FieldName "name")

_ColumnSchema_domain = (Core.FieldName "domain")

_ColumnSchema_isPrimaryKey = (Core.FieldName "isPrimaryKey")

-- | A mapping from certain columns of a source relation to primary key columns of a target relation
data ForeignKey = 
  ForeignKey {
    -- | The name of the target relation
    foreignKeyForeignRelation :: RelationName,
    foreignKeyKeys :: (Map ColumnName ColumnName)}
  deriving (Eq, Ord, Read, Show)

_ForeignKey = (Core.Name "hydra/langs/relationalModel.ForeignKey")

_ForeignKey_foreignRelation = (Core.FieldName "foreignRelation")

_ForeignKey_keys = (Core.FieldName "keys")

-- | A primary key of a relation, specified either as a single column, or as a list of columns
newtype PrimaryKey = 
  PrimaryKey {
    -- | A primary key of a relation, specified either as a single column, or as a list of columns
    unPrimaryKey :: [ColumnName]}
  deriving (Eq, Ord, Read, Show)

_PrimaryKey = (Core.Name "hydra/langs/relationalModel.PrimaryKey")

-- | A set of distinct n-tuples; a table
newtype Relation v = 
  Relation {
    unRelation :: (Set [v])}
  deriving (Eq, Ord, Read, Show)

_Relation = (Core.Name "hydra/langs/relationalModel.Relation")

-- | A unique relation (table) name
newtype RelationName = 
  RelationName {
    -- | A unique relation (table) name
    unRelationName :: String}
  deriving (Eq, Ord, Read, Show)

_RelationName = (Core.Name "hydra/langs/relationalModel.RelationName")

-- | An abstract relation; the name and columns of a relation without its actual data
data RelationSchema t = 
  RelationSchema {
    -- | A unique name for the relation
    relationSchemaName :: RelationName,
    -- | A list of column specifications
    relationSchemaColumns :: [ColumnSchema t],
    -- | Any number of primary keys for the relation, each of which must be valid for this relation
    relationSchemaPrimaryKeys :: [PrimaryKey],
    -- | Any number of foreign keys, each of which must be valid for both this relation and the target relation
    relationSchemaForeignKeys :: [ForeignKey]}
  deriving (Eq, Ord, Read, Show)

_RelationSchema = (Core.Name "hydra/langs/relationalModel.RelationSchema")

_RelationSchema_name = (Core.FieldName "name")

_RelationSchema_columns = (Core.FieldName "columns")

_RelationSchema_primaryKeys = (Core.FieldName "primaryKeys")

_RelationSchema_foreignKeys = (Core.FieldName "foreignKeys")

-- | A domain-unordered (string-indexed, rather than position-indexed) relation
newtype Relationship v = 
  Relationship {
    unRelationship :: (Set (Map ColumnName v))}
  deriving (Eq, Ord, Read, Show)

_Relationship = (Core.Name "hydra/langs/relationalModel.Relationship")

-- | An n-tuple which is an element of a given relation
newtype Row v = 
  Row {
    unRow :: [v]}
  deriving (Eq, Ord, Read, Show)

_Row = (Core.Name "hydra/langs/relationalModel.Row")