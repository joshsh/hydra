-- | A DSL for constructing Hydra types

{-# LANGUAGE FlexibleInstances #-} -- TODO: temporary, for IsString (Type Kv)
module Hydra.Dsl.Types where

import Hydra.Constants
import Hydra.Core

import qualified Data.List as L
import qualified Data.Map as M
import Data.String(IsString(..))


instance IsString (Type Kv) where fromString = var

infixr 0 >:
(>:) :: String -> Type Kv -> FieldType Kv
n >: t = field n t

infixr 0 -->
(-->) :: Type Kv -> Type Kv -> Type Kv
a --> b = function a b

(@@) :: Type Kv -> Type Kv -> Type Kv
f @@ x = apply f x

annot :: Kv -> Type Kv -> Type Kv
annot ann t = TypeAnnotated $ Annotated t ann

apply :: Type Kv -> Type Kv -> Type Kv
apply lhs rhs = TypeApplication (ApplicationType lhs rhs)

applyN :: [Type Kv] -> Type Kv
applyN ts = foldl apply (L.head ts) (L.tail ts)

bigfloat :: Type Kv
bigfloat = float FloatTypeBigfloat

bigint :: Type Kv
bigint = integer IntegerTypeBigint

binary :: Type Kv
binary = literal LiteralTypeBinary

boolean :: Type Kv
boolean = literal LiteralTypeBoolean

enum :: [String] -> Type Kv
enum names = union $ (`field` unit) <$> names

field :: String -> Type Kv -> FieldType Kv
field fn = FieldType (FieldName fn)

fieldsToMap :: [FieldType Kv] -> M.Map FieldName (Type Kv)
fieldsToMap fields = M.fromList $ (\(FieldType name typ) -> (name, typ)) <$> fields

float32 :: Type Kv
float32 = float FloatTypeFloat32

float64 :: Type Kv
float64 = float FloatTypeFloat64

float :: FloatType -> Type Kv
float = literal . LiteralTypeFloat

function :: Type Kv -> Type Kv -> Type Kv
function dom cod = TypeFunction $ FunctionType dom cod

functionN :: [Type Kv] -> Type Kv
functionN ts = L.foldl (\cod dom -> function dom cod) (L.head r) (L.tail r)
  where
    r = L.reverse ts

int16 :: Type Kv
int16 = integer IntegerTypeInt16

int32 :: Type Kv
int32 = integer IntegerTypeInt32

int64 :: Type Kv
int64 = integer IntegerTypeInt64

int8 :: Type Kv
int8 = integer IntegerTypeInt8

integer :: IntegerType -> Type Kv
integer = literal . LiteralTypeInteger

lambda :: String -> Type Kv -> Type Kv
lambda v body = TypeLambda $ LambdaType (Name v) body

lambdas :: [String] -> Type Kv -> Type Kv
lambdas vs body = L.foldr lambda body vs

list :: Type Kv -> Type Kv
list = TypeList

literal :: LiteralType -> Type Kv
literal = TypeLiteral

map :: Type Kv -> Type Kv -> Type Kv
map kt vt = TypeMap $ MapType kt vt

optional :: Type Kv -> Type Kv
optional = TypeOptional

pair :: Type Kv -> Type Kv -> Type Kv
pair a b = TypeProduct [a, b]

product :: [Type Kv] -> Type Kv
product = TypeProduct

record :: [FieldType Kv] -> Type Kv
record fields = TypeRecord $ RowType placeholderName Nothing fields

set :: Type Kv -> Type Kv
set = TypeSet

string :: Type Kv
string = literal LiteralTypeString

sum :: [Type Kv] -> Type Kv
sum = TypeSum

uint16 :: Type Kv
uint16 = integer IntegerTypeUint16

uint32 :: Type Kv
uint32 = integer IntegerTypeUint32

uint64 :: Type Kv
uint64 = integer IntegerTypeUint64

uint8 :: Type Kv
uint8 = integer IntegerTypeUint8

union :: [FieldType Kv] -> Type Kv
union fields = TypeUnion $ RowType placeholderName Nothing fields

unit :: Type Kv
unit = TypeRecord $ RowType (Name "hydra/core.UnitType") Nothing []

var :: String -> Type Kv
var = TypeVariable . Name

wrap :: Type Kv -> Type Kv
wrap = wrapWithName placeholderName

wrapWithName :: Name -> Type Kv -> Type Kv
wrapWithName name t = TypeWrap $ Nominal name t
