module Hydra.Dsl.Lib.Equality where

import Hydra.Core
import Hydra.Phantoms
import Hydra.Sources.Libraries
import qualified Hydra.Dsl.Terms as Terms

import Data.Int


equalBinary :: Datum (String -> String -> Bool)
equalBinary = Datum $ Terms.primitive _equality_equalBinary

equalBoolean :: Datum (Bool -> Bool -> Bool)
equalBoolean = Datum $ Terms.primitive _equality_equalBoolean

equalBigfloat :: Datum (Double -> Double -> Bool)
equalBigfloat = Datum $ Terms.primitive _equality_equalBigfloat

equalFloat32 :: Datum (Float -> Float -> Bool)
equalFloat32 = Datum $ Terms.primitive _equality_equalFloat32

equalFloat64 :: Datum (Double -> Double -> Bool)
equalFloat64 = Datum $ Terms.primitive _equality_equalFloat64

equalBigint :: Datum (Integer -> Integer -> Bool)
equalBigint = Datum $ Terms.primitive _equality_equalBigint

equalInt8 :: Datum (Int8 -> Int8 -> Bool)
equalInt8 = Datum $ Terms.primitive _equality_equalInt8

equalInt16 :: Datum (Int16 -> Int16 -> Bool)
equalInt16 = Datum $ Terms.primitive _equality_equalInt16

equalInt32 :: Datum (Int -> Int -> Bool)
equalInt32 = Datum $ Terms.primitive _equality_equalInt32

equalInt64 :: Datum (Int64 -> Int64 -> Bool)
equalInt64 = Datum $ Terms.primitive _equality_equalInt64

equalString :: Datum (String -> String -> Bool)
equalString = Datum $ Terms.primitive _equality_equalString

equalTerm :: Datum (Term Kv -> Term Kv -> Bool)
equalTerm = Datum $ Terms.primitive _equality_equalTerm

equalType :: Datum (Type Kv -> Type Kv -> Bool)
equalType = Datum $ Terms.primitive _equality_equalType

equalUint8 :: Datum (Int16 -> Int16 -> Bool)
equalUint8 = Datum $ Terms.primitive _equality_equalUint8

equalUint16 :: Datum (Int -> Int -> Bool)
equalUint16 = Datum $ Terms.primitive _equality_equalUint16

equalUint32 :: Datum (Int64 -> Int64 -> Bool)
equalUint32 = Datum $ Terms.primitive _equality_equalUint32

equalUint64 :: Datum (Integer -> Integer -> Bool)
equalUint64 = Datum $ Terms.primitive _equality_equalUint64

identity :: Datum (x -> x)
identity = Datum $ Terms.primitive _equality_identity

gtInt32 :: Datum (Int -> Int -> Bool)
gtInt32 = Datum $ Terms.primitive _equality_gtInt32

gteInt32 :: Datum (Int -> Int -> Bool)
gteInt32 = Datum $ Terms.primitive _equality_gteInt32

ltInt32 :: Datum (Int -> Int -> Bool)
ltInt32 = Datum $ Terms.primitive _equality_ltInt32

lteInt32 :: Datum (Int -> Int -> Bool)
lteInt32 = Datum $ Terms.primitive _equality_lteInt32
