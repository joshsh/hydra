-- | A basic TypeScript model, constructed on the basis of the typescriptlang.org documentation

module Hydra.Ext.TypeScript.Model where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

data FunctionType = 
  FunctionType {
    functionTypeParameters :: [Parameter],
    functionTypeRange :: Type}
  deriving (Eq, Ord, Read, Show)

_FunctionType = (Core.Name "hydra/ext/typeScript/model.FunctionType")

_FunctionType_parameters = (Core.Name "parameters")

_FunctionType_range = (Core.Name "range")

data Parameter = 
  Parameter {
    parameterName :: String,
    parameterType :: Type}
  deriving (Eq, Ord, Read, Show)

_Parameter = (Core.Name "hydra/ext/typeScript/model.Parameter")

_Parameter_name = (Core.Name "name")

_Parameter_type = (Core.Name "type")

data PrimitiveType = 
  -- | integers in the arbitrary precision format
  PrimitiveTypeBigint  |
  -- | true and false
  PrimitiveTypeBoolean  |
  -- | equivalent to the unit type
  PrimitiveTypeNull  |
  -- | a double-precision IEEE 754 floating point
  PrimitiveTypeNumber  |
  -- | similar to records
  PrimitiveTypeObject  |
  -- | an immutable UTF-16 string
  PrimitiveTypeString  |
  -- | a unique value usually used as a key
  PrimitiveTypeSymbol  |
  -- | also equivalent to the unit type
  PrimitiveTypeUndefined 
  deriving (Eq, Ord, Read, Show)

_PrimitiveType = (Core.Name "hydra/ext/typeScript/model.PrimitiveType")

_PrimitiveType_bigint = (Core.Name "bigint")

_PrimitiveType_boolean = (Core.Name "boolean")

_PrimitiveType_null = (Core.Name "null")

_PrimitiveType_number = (Core.Name "number")

_PrimitiveType_object = (Core.Name "object")

_PrimitiveType_string = (Core.Name "string")

_PrimitiveType_symbol = (Core.Name "symbol")

_PrimitiveType_undefined = (Core.Name "undefined")

data Type = 
  -- | mutable arrays, also written Array<T>
  TypeArray Type |
  -- | functions
  TypeFunction FunctionType |
  -- | the bottom type
  TypeNever  |
  -- | e.g. { property: Type }
  TypeObjectLiteral  |
  -- | A primitive type
  TypePrimitive PrimitiveType |
  -- | tuples, which are fixed-length but mutable
  TypeTuple [Type] |
  -- | The top type
  TypeUnknown  |
  -- | for functions with no documented return value
  TypeVoid 
  deriving (Eq, Ord, Read, Show)

_Type = (Core.Name "hydra/ext/typeScript/model.Type")

_Type_array = (Core.Name "array")

_Type_function = (Core.Name "function")

_Type_never = (Core.Name "never")

_Type_objectLiteral = (Core.Name "objectLiteral")

_Type_primitive = (Core.Name "primitive")

_Type_tuple = (Core.Name "tuple")

_Type_unknown = (Core.Name "unknown")

_Type_void = (Core.Name "void")