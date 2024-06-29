-- | A DSL for constructing Hydra types

{-# LANGUAGE FlexibleInstances #-} -- TODO: temporary, for IsString Type
module Hydra.Dsl.Types where

import Hydra.Constants
import Hydra.Core
import Hydra.Mantle
import qualified Hydra.Dsl.LiteralTypes as LiteralTypes

import qualified Data.List as L
import qualified Data.Map as M
import Data.String(IsString(..))


instance IsString Type where fromString = var

infixr 0 >:
(>:) :: String -> Type -> FieldType
n >: t = field n t

infixr 0 -->
(-->) :: Type -> Type -> Type
a --> b = function a b

(@@) :: Type -> Type -> Type
f @@ x = apply f x

annot :: M.Map String Term -> Type -> Type
annot ann t = TypeAnnotated $ Annotated t ann

apply :: Type -> Type -> Type
apply lhs rhs = TypeApplication (ApplicationType lhs rhs)

applyN :: [Type] -> Type
applyN ts = foldl apply (L.head ts) (L.tail ts)

bigfloat :: Type
bigfloat = literal LiteralTypes.bigfloat

bigint :: Type
bigint = integer IntegerTypeBigint

binary :: Type
binary = literal LiteralTypes.binary

boolean :: Type
boolean = literal LiteralTypes.boolean

enum :: [String] -> Type
enum names = union $ (`field` unit) <$> names

field :: String -> Type -> FieldType
field fn = FieldType (Name fn)

fieldsToMap :: [FieldType] -> M.Map Name Type
fieldsToMap fields = M.fromList $ (\(FieldType name typ) -> (name, typ)) <$> fields

float32 :: Type
float32 = literal LiteralTypes.float32

float64 :: Type
float64 = literal LiteralTypes.float64

float :: FloatType -> Type
float = literal . LiteralTypes.float

function :: Type -> Type -> Type
function dom cod = TypeFunction $ FunctionType dom cod

functionN :: [Type] -> Type
functionN ts = L.foldl (\cod dom -> function dom cod) (L.head r) (L.tail r)
  where
    r = L.reverse ts

int16 :: Type
int16 = literal LiteralTypes.int16

int32 :: Type
int32 = literal LiteralTypes.int32

int64 :: Type
int64 = literal LiteralTypes.int64

int8 :: Type
int8 = literal LiteralTypes.int8

integer :: IntegerType -> Type
integer = literal . LiteralTypes.integer

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

mono :: Type -> TypeScheme
mono = TypeScheme []

optional :: Type -> Type
optional = TypeOptional

pair :: Type -> Type -> Type
pair a b = TypeProduct [a, b]

poly :: [String] -> Type -> TypeScheme
poly vars = TypeScheme (Name <$> vars)

product :: [Type] -> Type
product = TypeProduct

record :: [FieldType] -> Type
record = recordWithName placeholderName

recordWithName :: Name -> [FieldType] -> Type
recordWithName name = TypeRecord . RowType name Nothing

set :: Type -> Type
set = TypeSet

string :: Type
string = literal LiteralTypes.string

sum :: [Type] -> Type
sum = TypeSum

uint16 :: Type
uint16 = literal LiteralTypes.uint16

uint32 :: Type
uint32 = literal LiteralTypes.uint32

uint64 :: Type
uint64 = literal LiteralTypes.uint64

uint8 :: Type
uint8 = literal LiteralTypes.uint8

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
