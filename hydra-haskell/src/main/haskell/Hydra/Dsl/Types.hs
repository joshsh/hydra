-- | A DSL for constructing Hydra types

module Hydra.Dsl.Types where

import Hydra.Constants
import Hydra.Core

import qualified Data.List as L
import qualified Data.Map as M
import Data.String(IsString(..))


instance IsString (Type a) where fromString = var

infixr 0 >:
(>:) :: String -> Type a -> FieldType a
n >: t = field n t

infixr 0 -->
(-->) :: Type a -> Type a -> Type a
a --> b = function a b

(@@) :: Type a -> Type a -> Type a
f @@ x = apply f x

annot :: a -> Type a -> Type a
annot ann t = TypeAnnotated $ Annotated t ann

apply :: Type a -> Type a -> Type a
apply lhs rhs = TypeApplication (ApplicationType lhs rhs)

applyN :: [Type a] -> Type a
applyN ts = foldl apply (L.head ts) (L.tail ts)

bigfloat :: Type a
bigfloat = float FloatTypeBigfloat

bigint :: Type a
bigint = integer IntegerTypeBigint

binary :: Type a
binary = literal LiteralTypeBinary

boolean :: Type a
boolean = literal LiteralTypeBoolean

enum :: [String] -> Type a
enum names = union $ (`field` unit) <$> names

field :: String -> Type a -> FieldType a
field fn = FieldType (FieldName fn)

fieldsToMap :: [FieldType a] -> M.Map FieldName (Type a)
fieldsToMap fields = M.fromList $ (\(FieldType name typ) -> (name, typ)) <$> fields

float32 :: Type a
float32 = float FloatTypeFloat32

float64 :: Type a
float64 = float FloatTypeFloat64

float :: FloatType -> Type a
float = literal . LiteralTypeFloat

function :: Type a -> Type a -> Type a
function dom cod = TypeFunction $ FunctionType dom cod

functionN :: [Type a] -> Type a
functionN ts = L.foldl (\cod dom -> function dom cod) (L.head r) (L.tail r)
  where
    r = L.reverse ts

int16 :: Type a
int16 = integer IntegerTypeInt16

int32 :: Type a
int32 = integer IntegerTypeInt32

int64 :: Type a
int64 = integer IntegerTypeInt64

int8 :: Type a
int8 = integer IntegerTypeInt8

integer :: IntegerType -> Type a
integer = literal . LiteralTypeInteger

lambda :: String -> Type a -> Type a
lambda v body = TypeLambda $ LambdaType (Name v) body

lambdas :: [String] -> Type a -> Type a
lambdas vs body = L.foldr lambda body vs

list :: Type a -> Type a
list = TypeList

literal :: LiteralType -> Type a
literal = TypeLiteral

map :: Type a -> Type a -> Type a
map kt vt = TypeMap $ MapType kt vt

optional :: Type a -> Type a
optional = TypeOptional

pair :: Type a -> Type a -> Type a
pair a b = TypeProduct [a, b]

product :: [Type a] -> Type a
product = TypeProduct

record :: [FieldType a] -> Type a
record fields = TypeRecord $ RowType placeholderName Nothing fields

set :: Type a -> Type a
set = TypeSet

string :: Type a
string = literal LiteralTypeString

sum :: [Type a] -> Type a
sum = TypeSum

uint16 :: Type a
uint16 = integer IntegerTypeUint16

uint32 :: Type a
uint32 = integer IntegerTypeUint32

uint64 :: Type a
uint64 = integer IntegerTypeUint64

uint8 :: Type a
uint8 = integer IntegerTypeUint8

union :: [FieldType a] -> Type a
union fields = TypeUnion $ RowType placeholderName Nothing fields

unit :: Type a
unit = TypeRecord $ RowType (Name "hydra/core.UnitType") Nothing []

var :: String -> Type a
var = TypeVariable . Name

wrap :: Type a -> Type a
wrap = wrapWithName placeholderName

wrapWithName :: Name -> Type a -> Type a
wrapWithName name t = TypeWrap $ Nominal name t
