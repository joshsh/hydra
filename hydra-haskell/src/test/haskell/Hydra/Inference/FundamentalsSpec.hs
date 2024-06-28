{-# LANGUAGE OverloadedStrings #-}

module Hydra.Inference.FundamentalsSpec where

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


checkLambdas :: H.SpecWith ()
checkLambdas = check "lambdas" $ do

    H.it "test #1" $
      expectPolytype
        (lambda "x" $ var "x")
        ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))
    H.it "test #2" $
      expectPolytype
        (lambda "x" $ int16 137)
        ["t0"] (Types.function (Types.var "t0") Types.int16)

checkLetTerms :: H.SpecWith ()
checkLetTerms = check "let terms" $ do

  H.it "test #0" $ do
    expectPolytype
      (letTerm (Name "x") (float32 42.0) (lambda "y" (lambda "z" (var "x"))))
      ["t0", "t1"] (Types.function (Types.var "t0") (Types.function (Types.var "t1") Types.float32))

  H.it "Empty let" $ do
    expectType
      ((int32 42) `with` [])
      Types.int32

  H.it "Trivial let" $ do
    expectType
      (var "foo" `with` [
        "foo">: int32 42])
      Types.int32

  H.it "Multiple references to a let-bound term" $
    expectType
      (list [var "foo", var "bar", var "foo"] `with` [
        "foo">: int32 42,
        "bar">: int32 137])
      (Types.list Types.int32)

  H.describe "Let-polymorphism" $ do
    H.it "test #1" $
      expectPolytype
        ((lambda "x" $ var "id" @@ (var "id" @@ var "x")) `with` [
          "id">: lambda "x" $ var "x"])
        ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))
    H.it "test #2" $
      expectType
        ((var "id" @@ (list [var "id" @@ int32 42])) `with` [
          "id">: lambda "x" $ var "x"])
        (Types.list Types.int32)
    H.it "test #3" $
      expectPolytype
        ((lambda "x" (var "id" @@ (list [var "id" @@ var "x"])))
          `with` [
            "id">: lambda "x" $ var "x"])
        ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #4" $
      expectType
        ((pair (var "id" @@ int32 42) (var "id" @@ string "foo"))
          `with` [
            "id">: lambda "x" $ var "x"])
        (Types.pair Types.int32 Types.string)
    H.it "test #5" $
      expectType
        ((pair (var "list" @@ int32 42) (var "list" @@ string "foo"))
          `with` [
            "list">: lambda "x" $ list [var "x"]])
        (Types.pair (Types.list Types.int32) (Types.list Types.string))
--    H.it "test #6" $
--      expectPolytype
--        ((var "f") `with` [
--          "singleton">: lambda "x" $ list [var "x"],
--          "f">: lambda "x" $ lambda "y" $ Terms.primitive _lists_cons
--            @@ (pair (var "singleton" @@ var "x") (var "singleton" @@ var "y"))
--            @@ (var "g" @@ var "x" @@ var "y"),
--          "g">: lambda "x" $ lambda "y" $ var "f" @@ int32 42 @@ var "y"])
--        ["t0"] (Types.list $ Types.pair Types.int32 (Types.var "t0"))

  H.describe "Recursive and mutually recursive let (@wisnesky's test cases)" $ do
--    H.it "test #1" $
--      expectPolytype
--        ((var "f") `with` [
--          "f">: lambda "x" $ lambda "y" (var "f" @@ int32 0 @@ var "x")])
--        ["t0"] (Types.function Types.int32 (Types.function Types.int32 (Types.var "t0")))
    H.it "test #2" $
      expectPolytype
        ((pair (var "f") (var "g")) `with` [
          "f">: var "g",
          "g">: var "f"])
        -- Note: GHC finds (a, b) rather than (a, a)
        -- Try: :t (let (f, g) = (g, f) in (f, g))
        ["t0"] (Types.pair (Types.var "t0") (Types.var "t0"))
--    H.it "test #3" $
--      expectPolytype
--        ((pair (var "f") (var "g")) `with` [
--          "f">: lambda "x" $ lambda "y" (var "g" @@ int32 0 @@ var "x"),
--          "g">: lambda "u" $ lambda "v" (var "f" @@ var "v" @@ int32 0)])
--        ["t0", "t1"] (Types.pair
--          (Types.function (Types.var "v0") (Types.function Types.int32 (Types.var "t1")))
--          (Types.function Types.int32 (Types.function (Types.var "v0") (Types.var "t1"))))

    -- letrec + = (\x . (\y . (S (+ (P x) y)))) in (+ (S (S 0)) (S 0))
--    let s = primitive _math_neg
--        p = primitive _math_neg
--    H.it "test #4" $
--      expectPolytype
--        ((var "plus" @@ (s @@ (s @@ int32 0)) @@ (s @@ int32 0)) `with` [
--          "plus">: lambda "x" $ lambda "y" (s @@ (var "plus" @@ (p @@ var "x") @@ var "y"))])
--        ["t0"] (Types.function Types.int32 $ Types.function (Types.var "t0") Types.int32)

    H.it "test #3" $
      expectType
        (int32 0 `with` [
          "id">: lambda "z" $ var "z",
          "f">: lambda "p0" $ pair (var "id" @@ var "p0") (var "id" @@ var "p0")])
        Types.int32
--    letrecs id = (\z. z)
--        f = (\p0. (pair (id p0) (id p0)))
--        in 0

checkLiterals :: H.SpecWith ()
checkLiterals = check "literal values" $ do

  check "individual literal terms" $ do
    H.it "test #1" $
      expectType
        (int32 42)
        Types.int32
    H.it "test #2" $
      expectType
        (string "foo")
        Types.string
    H.it "test #3" $
      expectType
        (boolean False)
        Types.boolean
    H.it "test #4" $
      expectType
        (float64 42.0)
        Types.float64

  H.it "randomly-generated literals" $
    QC.property $ \l -> expectType
      (TermLiteral l)
      (Types.literal $ literalType l)

checkPathologicalTerms :: H.SpecWith ()
checkPathologicalTerms = check "pathological terms" $ do

  H.describe "Infinite lists" $ do
    H.it "test #1" $
      expectType
        ((var "self") `with` [
          "self">: primitive _lists_cons @@ (int32 42) @@ (var "self")])
        (Types.list Types.int32)
    H.it "test #2" $
      expectPolytype
        (lambda "x" ((var "self") `with` [
          "self">: primitive _lists_cons @@ (var "x") @@ (var "self")]))
        ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #3" $
      expectPolytype
        ((lambda "x" $ var "self" @@ var "x") `with` [
          "self">: lambda "e" $ primitive _lists_cons @@ (var "e") @@ (var "self" @@ var "e")])
        ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #4" $
      expectType
        ((var "build" @@ int32 0) `with` [
          "build">: lambda "x" $ primitive _lists_cons @@ var "x" @@ (var "build" @@
            (primitive _math_add @@ var "x" @@ int32 1))])
        (Types.list Types.int32)

  -- TODO: this term *should* fail inference, but doesn't
--    H.it "Check self-application" $ do
--      expectFailure
--        (lambda "x" $ var "x" @@ var "x")

checkPolymorphism :: H.SpecWith ()
checkPolymorphism = check "polymorphism" $ do

  H.describe "Simple lists and optionals" $ do
    H.it "test #1" $
      expectPolytype
        (list [])
        ["t0"] (Types.list (Types.var "t0"))
    H.it "test #2" $
      expectPolytype
        (optional Nothing)
        ["t0"] (Types.optional (Types.var "t0"))
    H.it "test #3" $
      expectType
        (optional $ Just $ int32 42)
        (Types.optional Types.int32)

  H.describe "Lambdas, lists, and products" $ do
    H.it "test #1" $
      expectPolytype
        (lambda "x" $ var "x")
        ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))
    H.it "test #2" $
      expectPolytype
        (lambda "x" $ pair (var "x") (var "x"))
        ["t0"] (Types.function (Types.var "t0") (Types.pair (Types.var "t0") (Types.var "t0")))
    H.it "test #3" $
      expectPolytype
        (lambda "x" $ list [var "x"])
        ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #4" $
      expectPolytype
        (list [lambda "x" $ var "x", lambda "y" $ var "y"])
        ["t0"] (Types.list $ Types.function (Types.var "t0") (Types.var "t0"))
    H.it "test #5" $
      expectPolytype
        (list [lambda "x" $ lambda "y" $ pair (var "y") (var "x")])
        ["t0", "t1"] (Types.list $ Types.function (Types.var "t0") (Types.function (Types.var "t1") (Types.pair (Types.var "t1") (Types.var "t0"))))

  H.describe "Lambdas and application" $ do
    H.it "test #1" $
      expectType
        (lambda "x" (var "x") @@ string "foo")
        Types.string

  H.describe "Primitives and application" $ do
    H.it "test #1" $
      expectType
        (primitive _lists_concat @@ list [list [int32 42], list []])
        (Types.list Types.int32)

  H.describe "Lambdas and primitives" $ do
    H.it "test #1" $
      expectType
        (primitive _math_add)
        (Types.functionN [Types.int32, Types.int32, Types.int32])
    H.it "test #2" $
      expectType
        (lambda "x" (primitive _math_add @@ var "x"))
        (Types.functionN [Types.int32, Types.int32, Types.int32])
    H.it "test #3" $
      expectType
        (lambda "x" (primitive _math_add @@ var "x" @@ var "x"))
        (Types.function Types.int32 Types.int32)

  H.describe "Mixed expressions with lambdas, constants, and primitive functions" $ do
    H.it "test #1" $
      expectType
        (lambda "x" $
            (primitive _math_sub @@ (primitive _math_add @@ var "x" @@ var "x") @@ int32 1))
        (Types.function Types.int32 Types.int32)

checkPrimitives :: H.SpecWith ()
checkPrimitives = check "terms with primitive functions" $ do

  H.describe "Monomorphic primitive functions" $ do
    H.it "test #1" $
      expectType
        (primitive $ Name "hydra/lib/strings.length")
        (Types.function Types.string Types.int32)
    H.it "test #2" $
      expectType
        (primitive _math_sub)
        (Types.function Types.int32 (Types.function Types.int32 Types.int32))

  H.describe "Polymorphic primitive functions" $ do
    H.it "test #1" $
      expectPolytype
        (lambda "el" (primitive _lists_length @@ (list [var "el"])))
        ["t0"] (Types.function (Types.var "t0") Types.int32)
    H.it "test #2" $
      expectType
        (lambda "el" (primitive _lists_length @@ (list [int32 42, var "el"])))
        (Types.function Types.int32 Types.int32)
    H.it "test #3" $
      expectPolytype
        (primitive _lists_concat)
        ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #4" $
      expectPolytype
        (lambda "lists" (primitive _lists_concat @@ var "lists"))
        ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #5" $
      expectPolytype
        (lambda "lists" (primitive _lists_length @@ (primitive _lists_concat @@ var "lists")))
        ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") Types.int32)
    H.it "test #6" $
      expectPolytype
        (lambda "list" (primitive _lists_length @@ (primitive _lists_concat @@ list[var "list", list []])))
        ["t0"] (Types.function (Types.list $ Types.var "t0") Types.int32)
    H.it "test #7" $
      expectPolytype
        (lambda "list" (primitive _math_add
          @@ int32 1
          @@ (primitive _lists_length @@ (primitive _lists_concat @@ list[var "list", list []]))))
        ["t0"] (Types.function (Types.list $ Types.var "t0") Types.int32)
    H.it "test #8" $
      expectPolytype
        (lambda "lists" (primitive _lists_length @@ (primitive _lists_concat @@ var "lists")))
        ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") Types.int32)

spec :: H.Spec
spec = do
  checkLambdas
  checkLetTerms
  checkLiterals
  checkPathologicalTerms
  checkPolymorphism
  checkPrimitives
