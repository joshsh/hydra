-- | A JSON syntax model. See the BNF at https://www.json.org

module Hydra.Json where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | A JSON value
data Value = 
  ValueArray [Value] |
  ValueBoolean Bool |
  ValueNull  |
  ValueNumber Double |
  ValueObject (Map String Value) |
  ValueString String
  deriving (Eq, Ord, Read, Show)

_Value = (Core.Name "hydra/json.Value")

_Value_array = (Core.Name "array")

_Value_boolean = (Core.Name "boolean")

_Value_null = (Core.Name "null")

_Value_number = (Core.Name "number")

_Value_object = (Core.Name "object")

_Value_string = (Core.Name "string")
