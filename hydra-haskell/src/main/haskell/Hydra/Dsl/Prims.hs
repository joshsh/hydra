{-# LANGUAGE FlexibleInstances #-} -- for IsString with nontrivial parameters

-- | A DSL for constructing primitive function definitions
module Hydra.Dsl.Prims where

import Hydra.Compute
import Hydra.Core
import Hydra.Graph
import Hydra.CoreDecoding
import Hydra.CoreEncoding
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import Data.Int
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y
import Hydra.Rewriting (removeTermAnnotations)
import Data.String(IsString(..))

instance IsString (TermCoder Kv (Term)) where fromString = variable

bigfloat :: TermCoder Kv Double
bigfloat = TermCoder Types.bigfloat $ Coder encode decode
  where
    encode = Expect.bigfloat
    decode = pure . Terms.bigfloat

bigint :: TermCoder Kv Integer
bigint = TermCoder Types.bigint $ Coder encode decode
  where
    encode = Expect.bigint
    decode = pure . Terms.bigint

binary :: TermCoder Kv String
binary = TermCoder Types.binary $ Coder encode decode
  where
    encode = Expect.binary
    decode = pure . Terms.binary

boolean :: TermCoder Kv Bool
boolean = TermCoder Types.boolean $ Coder encode decode
  where
    encode = Expect.boolean
    decode = pure . Terms.boolean

float32 :: TermCoder Kv Float
float32 = TermCoder Types.float32 $ Coder encode decode
  where
    encode = Expect.float32
    decode = pure . Terms.float32

float64 :: TermCoder Kv Double
float64 = TermCoder Types.float64 $ Coder encode decode
  where
    encode = Expect.float64
    decode = pure . Terms.float64

flow :: TermCoder Kv s -> TermCoder Kv x -> TermCoder Kv (Flow s x)
flow states values = TermCoder (TypeVariable _Flow Types.@@ (termCoderType states) Types.@@ (termCoderType values)) $
    Coder encode decode
  where
    encode _ = fail $ "cannot currently encode flows from terms"
    decode _ = fail $ "cannot decode flows to terms"

function :: TermCoder Kv x -> TermCoder Kv y -> TermCoder Kv (x -> y)
function dom cod = TermCoder (Types.function (termCoderType dom) (termCoderType cod)) $ Coder encode decode
  where
    encode term = fail $ "cannot encode terms to functions"
    decode _ = fail $ "cannot decode functions to terms"

int8 :: TermCoder Kv Int8
int8 = TermCoder Types.int8 $ Coder encode decode
  where
    encode = Expect.int8
    decode = pure . Terms.int8

int16 :: TermCoder Kv Int16
int16 = TermCoder Types.int16 $ Coder encode decode
  where
    encode = Expect.int16
    decode = pure . Terms.int16

int32 :: TermCoder Kv Int
int32 = TermCoder Types.int32 $ Coder encode decode
  where
    encode = Expect.int32
    decode = pure . Terms.int32

int64 :: TermCoder Kv Int64
int64 = TermCoder Types.int64 $ Coder encode decode
  where
    encode = Expect.int64
    decode = pure . Terms.int64

list :: TermCoder Kv x -> TermCoder Kv [x]
list els = TermCoder (Types.list $ termCoderType els) $ Coder encode decode
  where
    encode = Expect.list (coderEncode $ termCoderCoder els)
    decode l = Terms.list <$> mapM (coderDecode $ termCoderCoder els) l

map :: (Ord k) => TermCoder Kv k -> TermCoder Kv v -> TermCoder Kv (M.Map k v)
map keys values = TermCoder (Types.map (termCoderType keys) (termCoderType values)) $ Coder encode decode
  where
    encode = Expect.map (coderEncode $ termCoderCoder keys) (coderEncode $ termCoderCoder values)
    decode m = Terms.map . M.fromList <$> mapM decodePair (M.toList m)
      where
        decodePair (k, v) = do
          ke <- (coderDecode $ termCoderCoder keys) k
          ve <- (coderDecode $ termCoderCoder values) v
          return (ke, ve)

optional :: TermCoder Kv x -> TermCoder Kv (Y.Maybe x)
optional mel = TermCoder (Types.optional $ termCoderType mel) $ Coder encode decode
  where
    encode = Expect.optional (coderEncode $ termCoderCoder mel)
    decode mv = Terms.optional <$> case mv of
      Nothing -> pure Nothing
      Just v -> Just <$> (coderDecode $ termCoderCoder mel) v

pair :: TermCoder Kv k -> TermCoder Kv v -> TermCoder Kv (k, v)
pair kCoder vCoder = TermCoder (Types.product [termCoderType kCoder, termCoderType vCoder]) $ Coder encode decode
  where
    encode = Expect.pair (coderEncode $ termCoderCoder kCoder) (coderEncode $ termCoderCoder vCoder)
    decode (k, v) = do
      kTerm <- coderDecode (termCoderCoder kCoder) k
      vTerm <- coderDecode (termCoderCoder vCoder) v
      return $ Terms.product [kTerm, vTerm]

prim0 :: Name -> TermCoder Kv x -> x -> Primitive Kv
prim0 = prim0Poly []

prim0Poly :: [String] -> Name -> TermCoder Kv x -> x -> Primitive Kv
prim0Poly vars name output value = Primitive name typ impl
  where
    typ = Types.lambdas vars $ termCoderType output
    impl _ = coderDecode (termCoderCoder output) value

prim1 :: Name -> TermCoder Kv x -> TermCoder Kv y -> (x -> y) -> Primitive Kv
prim1 = prim1Poly []

prim1Poly :: [String] -> Name -> TermCoder Kv x -> TermCoder Kv y -> (x -> y) -> Primitive Kv
prim1Poly vars name input1 output compute = Primitive name typ impl
  where
    typ = Types.lambdas vars $
      TypeFunction $ FunctionType (termCoderType input1) $ termCoderType output
    impl args = do
      Expect.nArgs 1 args
      arg1 <- coderEncode (termCoderCoder input1) (args !! 0)
      coderDecode (termCoderCoder output) $ compute arg1

prim2 :: Name -> TermCoder Kv x -> TermCoder Kv y -> TermCoder Kv z -> (x -> y -> z) -> Primitive Kv
prim2 = prim2Poly []

prim2Poly :: [String] -> Name -> TermCoder Kv x -> TermCoder Kv y -> TermCoder Kv z -> (x -> y -> z) -> Primitive Kv
prim2Poly vars name input1 input2 output compute = Primitive name typ impl
  where
    typ = Types.lambdas vars $
      TypeFunction $ FunctionType (termCoderType input1) (Types.function (termCoderType input2) (termCoderType output))
    impl args = do
      Expect.nArgs 2 args
      arg1 <- coderEncode (termCoderCoder input1) (args !! 0)
      arg2 <- coderEncode (termCoderCoder input2) (args !! 1)
      coderDecode (termCoderCoder output) $ compute arg1 arg2

prim2Interp :: [String] -> Name -> TermCoder Kv x -> TermCoder Kv y -> TermCoder Kv z -> (Term -> Term -> Flow (Graph Kv) (Term)) -> Primitive Kv
prim2Interp vars name input1 input2 output compute = Primitive name typ impl
  where
    typ = Types.lambdas vars $
      TypeFunction $ FunctionType (termCoderType input1) (Types.function (termCoderType input2) (termCoderType output))
    impl args = do
      Expect.nArgs 2 args
      compute (args !! 0) (args !! 1)

prim3 :: Name -> TermCoder Kv w -> TermCoder Kv x -> TermCoder Kv y -> TermCoder Kv z -> (w -> x -> y -> z) -> Primitive Kv
prim3 = prim3Poly []

prim3Poly :: [String] -> Name -> TermCoder Kv w -> TermCoder Kv x -> TermCoder Kv y -> TermCoder Kv z -> (w -> x -> y -> z) -> Primitive Kv
prim3Poly vars name input1 input2 input3 output compute = Primitive name typ impl
  where
    typ = Types.lambdas vars $
      TypeFunction $ FunctionType
        (termCoderType input1)
        (Types.function (termCoderType input2)
        (Types.function (termCoderType input3) (termCoderType output)))
    impl args = do
      Expect.nArgs 2 args
      arg1 <- coderEncode (termCoderCoder input1) (args !! 0)
      arg2 <- coderEncode (termCoderCoder input2) (args !! 1)
      arg3 <- coderEncode (termCoderCoder input3) (args !! 2)
      coderDecode (termCoderCoder output) $ compute arg1 arg2 arg3

set :: Ord x => TermCoder Kv x -> TermCoder Kv (S.Set x)
set els = TermCoder (Types.set $ termCoderType els) $ Coder encode decode
  where
    encode = Expect.set (coderEncode $ termCoderCoder els)
    decode s = Terms.set . S.fromList <$> mapM (coderDecode $ termCoderCoder els) (S.toList s)

string :: TermCoder Kv String
string = TermCoder Types.string $ Coder encode decode
  where
    encode = Expect.string
    decode = pure . Terms.string

term :: TermCoder Kv (Term)
term = TermCoder (Types.apply (TypeVariable _Term) (Types.var "a")) $ Coder encode decode
  where
    encode = pure
    decode = pure

type_ :: TermCoder Kv (Type)
type_ = TermCoder (Types.apply (TypeVariable _Type) (Types.var "a")) $ Coder encode decode
  where
    encode = coreDecodeType
    decode = pure . coreEncodeType

uint8 :: TermCoder Kv Int16
uint8 = TermCoder Types.uint8 $ Coder encode decode
  where
    encode = Expect.uint8
    decode = pure . Terms.uint8

uint16 :: TermCoder Kv Int
uint16 = TermCoder Types.uint16 $ Coder encode decode
  where
    encode = Expect.uint16
    decode = pure . Terms.uint16

uint32 :: TermCoder Kv Int64
uint32 = TermCoder Types.uint32 $ Coder encode decode
  where
    encode = Expect.uint32
    decode = pure . Terms.uint32

uint64 :: TermCoder Kv Integer
uint64 = TermCoder Types.uint64 $ Coder encode decode
  where
    encode = Expect.uint64
    decode = pure . Terms.uint64

variable :: String -> TermCoder Kv (Term)
variable v = TermCoder (Types.var v) $ Coder encode decode
  where
    encode = pure
    decode = pure
