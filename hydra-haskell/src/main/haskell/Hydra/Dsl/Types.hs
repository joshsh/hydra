-- | A DSL for constructing Hydra types

{-# LANGUAGE FlexibleInstances #-} -- TODO: temporary, for IsString (Type)
module Hydra.Dsl.Types where

import Hydra.Constants
import Hydra.Core

import qualified Data.List as L
import qualified Data.Map as M
import Data.String(IsString(..))


instance IsString (Type) where fromString = var

infixr 0 >:
(>:) :: String -> Type -> FieldType
n >: t = field n t

infixr 0 -->
(-->) :: Type -> Type -> Type
a --> b = function a b

(@@) :: Type -> Type -> Type
f @@ x = apply f x

annot :: Kv -> Type -> Type
annot ann t = TypeAnnotated $ Annotated t ann

apply :: Type -> Type -> Type
apply lhs rhs = TypeApplication (ApplicationType lhs rhs)

applyN :: [Type] -> Type
applyN ts = foldl apply (L.head ts) (L.tail ts)

bigfloat :: Type
bigfloat = float FloatTypeBigfloat

bigint :: Type
bigint = integer IntegerTypeBigint

binary :: Type
binary = literal LiteralTypeBinary

boolean :: Type
boolean = literal LiteralTypeBoolean

enum :: [String] -> Type
enum names = union $ (`field` unit) <$> names

field :: String -> Type -> FieldType
field fn = FieldType (FieldName fn)

fieldsToMap :: [FieldType] -> M.Map FieldName (Type)
fieldsToMap fields = M.fromList $ (\(FieldType name typ) -> (name, typ)) <$> fields

float32 :: Type
float32 = float FloatTypeFloat32

float64 :: Type
float64 = float FloatTypeFloat64

float :: FloatType -> Type
float = literal . LiteralTypeFloat

function :: Type -> Type -> Type
function dom cod = TypeFunction $ FunctionType dom cod

functionN :: [Type] -> Type
functionN ts = L.foldl (\cod dom -> function dom cod) (L.head r) (L.tail r)
  where
    r = L.reverse ts

int16 :: Type
int16 = integer IntegerTypeInt16

int32 :: Type
int32 = integer IntegerTypeInt32

int64 :: Type
int64 = integer IntegerTypeInt64

int8 :: Type
int8 = integer IntegerTypeInt8

integer :: IntegerType -> Type
integer = literal . LiteralTypeInteger

lambda :: String -> Type -> Type
lambda v body = TypeLambda $ LambdaType (Name v) body

lambdas :: [String] -> Type -> Type
lambdas vs body = L.foldr lambda body vs

list :: Type -> Type
list = TypeList

literal :: LiteralType -> Type
literal = TypeLiteral

map :: Type -> Type -> Type
map kt vt = TypeMap $ MapType kt vt

optional :: Type -> Type
optional = TypeOptional

pair :: Type -> Type -> Type
pair a b = TypeProduct [a, b]

product :: [Type] -> Type
product = TypeProduct

record :: [FieldType] -> Type
record fields = TypeRecord $ RowType placeholderName Nothing fields

set :: Type -> Type
set = TypeSet

string :: Type
string = literal LiteralTypeString

sum :: [Type] -> Type
sum = TypeSum

uint16 :: Type
uint16 = integer IntegerTypeUint16

uint32 :: Type
uint32 = integer IntegerTypeUint32

uint64 :: Type
uint64 = integer IntegerTypeUint64

uint8 :: Type
uint8 = integer IntegerTypeUint8

union :: [FieldType] -> Type
union fields = TypeUnion $ RowType placeholderName Nothing fields

unit :: Type
unit = TypeRecord $ RowType (Name "hydra/core.UnitType") Nothing []

var :: String -> Type
var = TypeVariable . Name

wrap :: Type -> Type
wrap = wrapWithName placeholderName

wrapWithName :: Name -> Type -> Type
wrapWithName name t = TypeWrap $ Nominal name t
