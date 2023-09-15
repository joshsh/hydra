-- | A DSL for constructing Hydra terms

{-# LANGUAGE FlexibleInstances #-} -- TODO: temporary, for IsString (Term Kv)
module Hydra.Dsl.Terms where

import Hydra.Compute
import Hydra.Constants
import Hydra.Core
import Hydra.Graph
import qualified Hydra.Dsl.Literals as Literals

import Prelude hiding (map)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y
import qualified Control.Monad as CM
import Data.Int
import Data.String(IsString(..))


instance IsString (Term Kv) where fromString = string

(@@) :: Term Kv -> Term Kv -> Term Kv
f @@ x = apply f x

(<.>) :: Term Kv -> Term Kv -> Term Kv
f <.> g = compose f g

infixr 0 >:
(>:) :: String -> Term Kv -> Field Kv
n >: t = field n t

annot :: Kv -> Term Kv -> Term Kv
annot ann t = TermAnnotated $ Annotated t ann

apply :: Term Kv -> Term Kv -> Term Kv
apply func arg = TermApplication $ Application func arg

bigfloat :: Double -> Term Kv
bigfloat = literal . Literals.bigfloat

bigint :: Integer -> Term Kv
bigint = literal . Literals.bigint

binary :: String -> Term Kv
binary = literal . Literals.binary

boolean :: Bool -> Term Kv
boolean = literal . Literals.boolean

compose :: Term Kv -> Term Kv -> Term Kv
compose f g = lambda "x" $ apply f (apply g $ var "x")

constant :: Term Kv -> Term Kv
constant = lambda ignoredVariable

elimination :: Elimination Kv -> Term Kv
elimination = TermFunction . FunctionElimination

false :: Term Kv
false = boolean False

field :: String -> Term Kv -> Field Kv
field n = Field (FieldName n)

fieldsToMap :: [Field Kv] -> M.Map FieldName (Term Kv)
fieldsToMap fields = M.fromList $ (\(Field name term) -> (name, term)) <$> fields

float32 :: Float -> Term Kv
float32 = literal . Literals.float32

float64 :: Double -> Term Kv
float64 = literal . Literals.float64

float :: FloatValue -> Term Kv
float = literal . Literals.float

fold :: Term Kv -> Term Kv
fold = TermFunction . FunctionElimination . EliminationList

identity :: Term Kv
identity = lambda "x" $ var "x"

inject :: Name -> Field Kv -> Term Kv
inject tname = TermUnion . Injection tname

int16 :: Int16 -> Term Kv
int16 = literal . Literals.int16

int32 :: Int -> Term Kv
int32 = literal . Literals.int32

int64 :: Int64 -> Term Kv
int64 = literal . Literals.int64

int8 :: Int8 -> Term Kv
int8 = literal . Literals.int8

integer :: IntegerValue -> Term Kv
integer = literal . Literals.integer

just :: Term Kv -> Term Kv
just = optional . Just

lambda :: String -> Term Kv -> Term Kv
lambda param body = TermFunction $ FunctionLambda $ Lambda (Name param) body

-- Construct a 'let' term with a single binding
letTerm :: Name -> Term Kv -> Term Kv -> Term Kv
letTerm v t1 t2 = TermLet $ Let (M.fromList [(v, t1)]) t2

list :: [Term Kv] -> Term Kv
list = TermList

literal :: Literal -> Term Kv
literal = TermLiteral

map :: M.Map (Term Kv) (Term Kv) -> Term Kv
map = TermMap

mapTerm :: M.Map (Term Kv) (Term Kv) -> Term Kv
mapTerm = TermMap

match :: Name -> Maybe (Term Kv) -> [Field Kv] -> Term Kv
match tname def fields = TermFunction $ FunctionElimination $ EliminationUnion $ CaseStatement tname def fields

matchOpt :: Term Kv -> Term Kv -> Term Kv
matchOpt n j = TermFunction $ FunctionElimination $ EliminationOptional $ OptionalCases n j

matchWithVariants :: Name -> Maybe (Term Kv) -> [(FieldName, FieldName)] -> Term Kv
matchWithVariants tname def pairs = match tname def (toField <$> pairs)
  where
    toField (from, to) = Field from $ constant $ unitVariant tname to

nothing :: Term Kv
nothing = optional Nothing

optional :: Y.Maybe (Term Kv) -> Term Kv
optional = TermOptional

pair :: Term Kv -> Term Kv -> Term Kv
pair a b = TermProduct [a, b]

primitive :: Name -> Term Kv
primitive = TermFunction . FunctionPrimitive

product :: [Term Kv] -> Term Kv
product = TermProduct

project :: Name -> FieldName -> Term Kv
project tname fname = TermFunction $ FunctionElimination $ EliminationRecord $ Projection tname fname

record :: Name -> [Field Kv] -> Term Kv
record tname fields = TermRecord $ Record tname fields

set :: S.Set (Term Kv) -> Term Kv
set = TermSet

string :: String -> Term Kv
string = TermLiteral . LiteralString

sum :: Int -> Int -> Term Kv -> Term Kv
sum i s term = TermSum $ Sum i s term

true :: Term Kv
true = boolean True

uint16 :: Int -> Term Kv
uint16 = literal . Literals.uint16

uint32 :: Int64 -> Term Kv
uint32 = literal . Literals.uint32

uint64 :: Integer -> Term Kv
uint64 = literal . Literals.uint64

uint8 :: Int16 -> Term Kv
uint8 = literal . Literals.uint8

unit :: Term Kv
unit = TermRecord $ Record _UnitType []

unitVariant :: Name -> FieldName -> Term Kv
unitVariant tname fname = variant tname fname unit

untuple :: Int -> Int -> Term Kv
untuple arity idx = TermFunction $ FunctionElimination $ EliminationProduct $ TupleProjection arity idx

unwrap :: Name -> Term Kv
unwrap = TermFunction . FunctionElimination . EliminationWrap

var :: String -> Term Kv
var = TermVariable . Name

variant :: Name -> FieldName -> Term Kv -> Term Kv
variant tname fname term = TermUnion $ Injection tname $ Field fname term

with :: Term Kv -> [Field Kv] -> Term Kv
env `with` bindings = TermLet $ Let (M.fromList $ toPair <$> bindings) env
  where
     toPair (Field name value) = (Name $ unFieldName name, value)

withVariant :: Name -> FieldName -> Term Kv
withVariant tname = constant . unitVariant tname

wrap :: Name -> Term Kv -> Term Kv
wrap name term = TermWrap $ Nominal name term
