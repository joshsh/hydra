-- | Phantom types for use in model definitions

module Hydra.Phantoms where

import qualified Hydra.Compute as Compute
import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | An association of a field name (as in a case statement) with a phantom type
newtype Case a = 
  Case {
    unCase :: Core.FieldName}
  deriving (Eq, Ord, Read, Show)

_Case = (Core.Name "hydra/phantoms.Case")

-- | An association of a term with a phantom type
newtype Datum a = 
  Datum {
    unDatum :: (Core.Term Compute.Kv)}
  deriving (Eq, Ord, Read, Show)

_Datum = (Core.Name "hydra/phantoms.Datum")

-- | An association with a named term with a phantom type
data Definition a = 
  Definition {
    definitionName :: Core.Name,
    definitionDatum :: (Datum a)}
  deriving (Eq, Ord, Read, Show)

_Definition = (Core.Name "hydra/phantoms.Definition")

_Definition_name = (Core.FieldName "name")

_Definition_datum = (Core.FieldName "datum")

-- | An association with a term-level field with a phantom type
newtype Fld a = 
  Fld {
    unFld :: (Core.Field Compute.Kv)}
  deriving (Eq, Ord, Read, Show)

_Fld = (Core.Name "hydra/phantoms.Fld")

-- | A pure association with a phantom type
data Reference a = 
  Reference {}
  deriving (Eq, Ord, Read, Show)

_Reference = (Core.Name "hydra/phantoms.Reference")