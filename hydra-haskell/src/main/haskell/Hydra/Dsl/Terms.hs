-- | A DSL for constructing Hydra terms

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


instance IsString (Term a) where fromString = string

(@@) :: Term a -> Term a -> Term a
f @@ x = apply f x

(<.>) :: Term a -> Term a -> Term a
f <.> g = compose f g

infixr 0 >:
(>:) :: String -> Term a -> Field a
n >: t = field n t

annot :: a -> Term a -> Term a
annot ann t = TermAnnotated $ Annotated t ann

apply :: Term a -> Term a -> Term a
apply func arg = TermApplication $ Application func arg

bigfloat :: Double -> Term a
bigfloat = literal . Literals.bigfloat

bigint :: Integer -> Term a
bigint = literal . Literals.bigint

binary :: String -> Term a
binary = literal . Literals.binary

boolean :: Bool -> Term a
boolean = literal . Literals.boolean

compose :: Term a -> Term a -> Term a
compose f g = lambda "x" $ apply f (apply g $ var "x")

constant :: Term a -> Term a
constant = lambda ignoredVariable

elimination :: Elimination a -> Term a
elimination = TermFunction . FunctionElimination

false :: Term a
false = boolean False

field :: String -> Term a -> Field a
field n = Field (FieldName n)

fieldsToMap :: [Field a] -> M.Map FieldName (Term a)
fieldsToMap fields = M.fromList $ (\(Field name term) -> (name, term)) <$> fields

float32 :: Float -> Term a
float32 = literal . Literals.float32

float64 :: Double -> Term a
float64 = literal . Literals.float64

float :: FloatValue -> Term a
float = literal . Literals.float

fold :: Term a -> Term a
fold = TermFunction . FunctionElimination . EliminationList

identity :: Term a
identity = lambda "x" $ var "x"

inject :: Name -> Field a -> Term a
inject tname = TermUnion . Injection tname

int16 :: Int16 -> Term a
int16 = literal . Literals.int16

int32 :: Int -> Term a
int32 = literal . Literals.int32

int64 :: Int64 -> Term a
int64 = literal . Literals.int64

int8 :: Int8 -> Term a
int8 = literal . Literals.int8

integer :: IntegerValue -> Term a
integer = literal . Literals.integer

just :: Term a -> Term a
just = optional . Just

lambda :: String -> Term a -> Term a
lambda param body = TermFunction $ FunctionLambda $ Lambda (Name param) body

-- Construct a 'let' term with a single binding
letTerm :: Name -> Term a -> Term a -> Term a
letTerm v t1 t2 = TermLet $ Let (M.fromList [(v, t1)]) t2

list :: [Term a] -> Term a
list = TermList

literal :: Literal -> Term a
literal = TermLiteral

map :: M.Map (Term a) (Term a) -> Term a
map = TermMap

mapTerm :: M.Map (Term a) (Term a) -> Term a
mapTerm = TermMap

match :: Name -> Maybe (Term a) -> [Field a] -> Term a
match tname def fields = TermFunction $ FunctionElimination $ EliminationUnion $ CaseStatement tname def fields

matchOpt :: Term a -> Term a -> Term a
matchOpt n j = TermFunction $ FunctionElimination $ EliminationOptional $ OptionalCases n j

matchWithVariants :: Name -> Maybe (Term a) -> [(FieldName, FieldName)] -> Term a
matchWithVariants tname def pairs = match tname def (toField <$> pairs)
  where
    toField (from, to) = Field from $ constant $ unitVariant tname to

nothing :: Term a
nothing = optional Nothing

optional :: Y.Maybe (Term a) -> Term a
optional = TermOptional

pair :: Term a -> Term a -> Term a
pair a b = TermProduct [a, b]

primitive :: Name -> Term a
primitive = TermFunction . FunctionPrimitive

product :: [Term a] -> Term a
product = TermProduct

project :: Name -> FieldName -> Term a
project tname fname = TermFunction $ FunctionElimination $ EliminationRecord $ Projection tname fname

record :: Name -> [Field a] -> Term a
record tname fields = TermRecord $ Record tname fields

set :: S.Set (Term a) -> Term a
set = TermSet

string :: String -> Term a
string = TermLiteral . LiteralString

sum :: Int -> Int -> Term a -> Term a
sum i s term = TermSum $ Sum i s term

true :: Term a
true = boolean True

uint16 :: Int -> Term a
uint16 = literal . Literals.uint16

uint32 :: Int64 -> Term a
uint32 = literal . Literals.uint32

uint64 :: Integer -> Term a
uint64 = literal . Literals.uint64

uint8 :: Int16 -> Term a
uint8 = literal . Literals.uint8

unit :: Term a
unit = TermRecord $ Record _UnitType []

unitVariant :: Name -> FieldName -> Term a
unitVariant tname fname = variant tname fname unit

untuple :: Int -> Int -> Term a
untuple arity idx = TermFunction $ FunctionElimination $ EliminationProduct $ TupleProjection arity idx

unwrap :: Name -> Term a
unwrap = TermFunction . FunctionElimination . EliminationWrap

var :: String -> Term a
var = TermVariable . Name

variant :: Name -> FieldName -> Term a -> Term a
variant tname fname term = TermUnion $ Injection tname $ Field fname term

with :: Term a -> [Field a] -> Term a
env `with` bindings = TermLet $ Let (M.fromList $ toPair <$> bindings) env
  where
     toPair (Field name value) = (Name $ unFieldName name, value)

withVariant :: Name -> FieldName -> Term a
withVariant tname = constant . unitVariant tname

wrap :: Name -> Term a -> Term a
wrap name term = TermWrap $ Nominal name term
