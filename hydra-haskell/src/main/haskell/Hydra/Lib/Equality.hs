-- | Haskell implementations of hydra/lib/equality primitives. These simply make use of derived Eq.

module Hydra.Lib.Equality where

import Hydra.Core

import Data.Int


equalBinary :: String -> String -> Bool
equalBinary = (==)

equalBoolean :: Bool -> Bool -> Bool
equalBoolean = (==)

equalBigfloat :: Double -> Double -> Bool
equalBigfloat = (==)

equalFloat32 :: Float -> Float -> Bool
equalFloat32 = (==)

equalFloat64 :: Double -> Double -> Bool
equalFloat64 = (==)

equalBigint :: Integer -> Integer -> Bool
equalBigint = (==)

equalInt8 :: Int8 -> Int8 -> Bool
equalInt8 = (==)

equalInt16 :: Int16 -> Int16 -> Bool
equalInt16 = (==)

equalInt32 :: Int -> Int -> Bool
equalInt32 = (==)

equalInt64 :: Int64 -> Int64 -> Bool
equalInt64 = (==)

equalUint8 :: Int16 -> Int16 -> Bool
equalUint8 = (==)

equalUint16 :: Int -> Int -> Bool
equalUint16 = (==)

equalUint32 :: Int64 -> Int64 -> Bool
equalUint32 = (==)

equalUint64 :: Integer -> Integer -> Bool
equalUint64 = (==)

equalString :: String -> String -> Bool
equalString = (==)

equalTerm :: Term -> Term -> Bool
equalTerm = (==)

equalType :: Type Kv -> Type Kv -> Bool
equalType = (==)

gtInt32 :: Int -> Int -> Bool
gtInt32 = (>)

gteInt32 :: Int -> Int -> Bool
gteInt32 = (>=)

identity :: x -> x
identity = id

ltInt32 :: Int -> Int -> Bool
ltInt32 = (<)

lteInt32 :: Int -> Int -> Bool
lteInt32 = (<=)
