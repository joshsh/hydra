{-# LANGUAGE OverloadedStrings #-}

module Hydra.Inference.AlgebraicTypesSpec where

import Hydra.Kernel
import Hydra.Sources.Libraries
import Hydra.Inference
import Hydra.TestUtils
import Hydra.TestData
import qualified Hydra.Dsl.Expect as Expect
import Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Annotations as Ann
import qualified Hydra.Dsl.Types as Types
import Hydra.Dsl.ShorthandTypes
import Hydra.Inference.InferenceTestUtils

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad


checkFolds :: H.SpecWith ()
checkFolds = check "list eliminations (folds)" $ do

    let fun = Terms.fold $ primitive _math_add

    H.it "test #1" $
      expectType
        fun
        (Types.functionN [Types.int32, Types.list Types.int32, Types.int32])
    H.it "test #2" $
      expectType
        (fun @@ int32 0)
        (Types.function (Types.list Types.int32) Types.int32)
    H.it "test #3" $
      expectType
        (fun @@ int32 0 @@ (list (int32 <$> [1, 2, 3, 4, 5])))
        Types.int32

checkLists :: H.SpecWith ()
checkLists = check "list terms" $ do

  H.it "List of strings" $
    expectType
      (list [string "foo", string "bar"])
      (Types.list Types.string)
  H.it "List of lists of strings" $
    expectType
      (list [list [string "foo"], list []])
      (Types.list $ Types.list Types.string)
  H.it "Empty list" $
    expectPolytype
      (list [])
      ["t0"] (Types.list $ Types.var "t0")
  H.it "List containing an empty list" $
    expectPolytype
      (list [list []])
      ["t0"] (Types.list $ Types.list $ Types.var "t0")
  H.it "Lambda producing a polymorphic list" $
    expectPolytype
      (lambda "x" (list [var "x"]))
      ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
  H.it "Lambda producing a list of integers" $
    expectType
      (lambda "x" (list [var "x", int32 42]))
      (Types.function Types.int32 $ Types.list Types.int32)
  H.it "List with repeated variables" $
    expectType
      (lambda "x" (list [var "x", string "foo", var "x"]))
      (Types.function Types.string (Types.list Types.string))

checkMaps :: H.SpecWith ()
checkMaps = check "maps" $ do

    H.it "test #1" $
      expectType
        (mapTerm $ M.fromList [(string "firstName", string "Arthur"), (string "lastName", string "Dent")])
        (Types.map Types.string Types.string)
    H.it "test #2" $
      expectPolytype
        (mapTerm M.empty)
        ["t0", "t1"] (Types.map (Types.var "t0") (Types.var "t1"))
    H.it "test #3" $
      expectPolytype
        (lambda "x" (lambda "y" (mapTerm $ M.fromList
          [(var "x", float64 0.1), (var "y", float64 0.2)])))
        ["t0"] (Types.function (Types.var "t0") (Types.function (Types.var "t0") (Types.map (Types.var "t0") Types.float64)))

checkOptionals :: H.SpecWith ()
checkOptionals = check "optionals" $ do

  H.it "test #1" $
    expectType
      (optional $ Just $ int32 42)
      (Types.optional Types.int32)
  H.it "test #2" $
    expectPolytype
      (optional Nothing)
      ["t0"] (Types.optional $ Types.var "t0")

checkProducts :: H.SpecWith ()
checkProducts = check "product terms" $ do

  H.it "Empty product" $ do
    expectType
      (Terms.product [])
      (Types.product [])

  H.describe "Non-empty, monotyped products" $ do
    H.it "test #1" $
      expectType
        (Terms.product [string "foo", int32 42])
        (Types.product [Types.string, Types.int32])
    H.it "test #2" $
      expectType
        (Terms.product [string "foo", list [float32 42.0, float32 137.0]])
        (Types.product [Types.string, Types.list Types.float32])
    H.it "test #3" $
      expectType
        (Terms.product [string "foo", int32 42, list [float32 42.0, float32 137.0]])
        (Types.product [Types.string, Types.int32, Types.list Types.float32])

  H.describe "Polytyped products" $ do
    H.it "test #1" $
      expectPolytype
        (Terms.product [list [], string "foo"])
        ["t0"] (Types.product [Types.list $ Types.var "t0", Types.string])
    H.it "test #2" $
      expectPolytype
        (Terms.product [int32 42, "foo", list []])
        ["t0"] (Types.product [Types.int32, Types.string, Types.list $ Types.var "t0"])

  H.describe "Pairs" $ do
    H.it "test #1" $
      expectType
        (pair (int32 42) "foo")
        (Types.pair Types.int32 Types.string)
    H.it "test #2" $
      expectPolytype
        (pair (list []) "foo")
        ["t0"] (Types.pair (Types.list $ Types.var "t0") Types.string)
    H.it "test #3" $
      expectPolytype
        (pair (list []) (list []))
        ["t0", "t1"] (Types.pair (Types.list $ Types.var "t0") (Types.list $ Types.var "t1"))

checkSets :: H.SpecWith ()
checkSets = check "sets" $ do

  H.it "test #1" $
    expectType
      (set $ S.fromList [boolean True])
      (Types.set Types.boolean)
  H.it "test #2" $
    expectPolytype
      (set $ S.fromList [set S.empty])
      ["t0"] (Types.set $ Types.set $ Types.var "t0")

checkSums :: H.SpecWith ()
checkSums = check "sum terms" $ do

  H.describe "Singleton sum terms" $ do
    H.it "test #1" $
      expectType
        (Terms.sum 0 1 $ string "foo")
        (Types.sum [Types.string])
    H.it "test #2" $
      expectPolytype
        (Terms.sum 0 1 $ list [])
        ["t0"] (Types.sum [Types.list $ Types.var "t0"])

  H.describe "Non-singleton sum terms" $ do
    H.it "test #1" $
      expectPolytype
        (Terms.sum 0 2 $ string "foo")
        ["t0"] (Types.sum [Types.string, Types.var "t0"])
    H.it "test #2" $
      expectPolytype
        (Terms.sum 1 2 $ string "foo")
        ["t0"] (Types.sum [Types.var "t0", Types.string])

spec :: H.Spec
spec = do
  checkFolds
  checkLists
  checkMaps
  checkOptionals
  checkProducts
  checkSets
  checkSums
