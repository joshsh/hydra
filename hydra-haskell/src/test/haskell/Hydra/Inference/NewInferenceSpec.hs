module Hydra.Inference.NewInferenceSpec where

import Hydra.Kernel
import Hydra.NewInference
import qualified Hydra.Tier1 as Tier1

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Map as M
import qualified Test.Hspec as H
import qualified Test.HUnit.Lang as HL
import qualified Hydra.Dsl.Types as Types


-- @wisnesky's original Algorithm W test cases, modified so as to normalize type variables
-- Polymorphic recursion is excluded; see checkPolymorphicRecursion
checkAlgorithmW :: H.SpecWith ()
checkAlgorithmW = H.describe "Check System F syntax" $ do
  --Untyped input:
  --	(\x. x)
  --System F type:
  -- 	(v0 -> v0)
  testCase "0"
    (lambda "x" $ var "x")
    (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.var "t0"))

  --Untyped input:
  --	letrecs foo = (\x. x)
  --		in 42
  --System F type:
  -- 	Nat
  testCase "1"
    (int32 32 `with` [
      "foo">: lambda "x" $ var "x"])
    (Types.mono Types.int32)

  --Untyped input:
  --	let f = (\x. x) in (f 0)
  --System F type:
  -- 	Nat
  testCase "2"
    ((var "f" @@ int32 0) `with` [
      "f">: lambda "x" $ var "x"])
    (Types.mono Types.int32)

  --Untyped input:
  --	let f = ((\x. x) 0) in f
  --System F type:
  -- 	Nat
  testCase "3"
    (var "f" `with` [
      "f">: (lambda "x" $ var "x") @@ int32 0])
    (Types.mono Types.int32)

  testCase "3.5"
    (lambda "x" $ list [var "x"])
    (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.list (Types.var "t0")))

  --Untyped input:
  --	let sng = (\x. (cons x nil)) in sng
  --System F type:
  -- 	(v5 -> (List v5))
  testCase "4"
    (var "sng" `with` [
      "sng">: lambda "x" $ list [var "x"]])
    (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.list (Types.var "t0")))

  --Untyped input:
  --	let sng = (\x. (cons x nil)) in (pair (sng 0) (sng alice))
  --System F type:
  -- 	((List Nat) * (List String))
  testCase "5"
    (pair (var "sng" @@ int32 0) (var "sng" @@ string "alice") `with` [
      "sng">: lambda "x" $ list [var "x"]])
    (Types.mono $ Types.pair (Types.list Types.int32) (Types.list Types.string))

  --Untyped input:
  --	letrecs + = (\x. (\y. (S (+ (P x) y))))
  --		in (+ (S (S 0)) (S 0))
  --System F type:
  -- 	Nat
  testCase "6"
    ((var "+" @@ (primSucc @@ (primSucc @@ int32 0)) @@ (primSucc @@ int32 0)) `with` [
      "+">: lambda "x" $ lambda "y" (primSucc @@ (var "+" @@ (primPred @@ var "x") @@ var "y"))])
    (Types.mono Types.int32)

checkApplication :: H.SpecWith ()
checkApplication = H.describe "Check application terms" $ do

  testCase "1"
    ((lambda "x" $ var "x") @@ (int32 42))
    (Types.mono Types.int32)

  testCase "2"
    (lambda "y" ((lambda "x" $ list [var "x"]) @@ (var "y")))
    (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.list $ Types.var "t0"))

checkLambdas :: H.SpecWith ()
checkLambdas = H.describe "Check lambda expressions" $ do

  testCase "1"
     (lambda "x" $ int32 42)
     (Types.poly ["t0"] (Types.function (Types.var "t0") Types.int32))

  testCase "2"
    (lambda "x" $ var "x")
    (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.var "t0"))

  testCase "3"
    (lambda "x" $ lambda "y" $ var "x")
    (Types.poly ["t0", "t1"] $ Types.function (Types.var "t0") (Types.function (Types.var "t1") (Types.var "t0")))

checkLists :: H.SpecWith ()
checkLists = H.describe "Check lists" $ do

  testCase "0"
    (list [])
    (Types.poly ["t0"] (Types.list $ Types.var "t0"))

  testCase "1"
    (list [int32 42])
    (Types.mono (Types.list Types.int32))

  testCase "2"
    (list [int32 42, int32 43])
    (Types.mono (Types.list Types.int32))

  testCase "3"
    (list [list []])
    (Types.poly ["t0"] (Types.list $ Types.list $ Types.var "t0"))

  testCase "4"
    (list [list [], list []])
    (Types.poly ["t0"] (Types.list $ Types.list $ Types.var "t0"))

  testCase "5"
    (list [list [], list [int32 42]])
    (Types.mono (Types.list $ Types.list Types.int32))

checkLambdasAndLists :: H.SpecWith ()
checkLambdasAndLists = H.describe "Check lambdas with lists" $ do

  testCase "0"
    (lambda "x" $ list [var "x"])
    (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.list (Types.var "t0")))

  testCase "1"
    (lambda "x" $ list [var "x", var "x"])
    (Types.poly ["t0"] $ Types.function (Types.var "t0") (Types.list (Types.var "t0")))

  testCase "2"
    (lambda "x" $ list [var "x", int32 42])
    (Types.mono $ Types.function Types.int32 (Types.list Types.int32))

  testCase "3"
    (lambda "x" $ lambda "y" $ list [var "x", int32 42, var "y"])
    (Types.mono $ Types.function Types.int32 $ Types.function Types.int32 $ Types.list Types.int32)

-- Additional test cases from @wisnesky which involve polymorphic recursion,
-- and so are not expected to be supported.
checkPolymorphicRecursion :: H.SpecWith ()
checkPolymorphicRecursion = H.describe "Check selected polymorphic recursion cases" $ do
  --Untyped input:
  --	letrecs f = (\x. (\y. (f 0 x)))
  --		in f
  --System F type:
  -- 	(Nat -> (Nat -> v5))
  testCase "7"
    (var "f" `with` [
      "f">: lambda "x" $ lambda "y" (var "f" @@ int32 0 @@ var "x")])
    (Types.poly ["t0"] $ Types.function Types.int32 (Types.function Types.int32 (Types.var "t0")))

  --Untyped input:
  --	letrecs f = (\x. (\y. (g 0 x)))
  --		g = (\u. (\v. (f v 0)))
  --		in (pair f g)
  --System F type:
  -- 	((v12 -> (Nat -> v13)) * (Nat -> (v15 -> v16)))
  testCase "9"
    ((pair (var "f") (var "g")) `with` [
      "f">: lambda "x" $ lambda "y" (var "g" @@ int32 0 @@ var "x"),
      "g">: lambda "u" $ lambda "v" (var "f" @@ var "v" @@ int32 0)])
    (Types.poly ["t0", "t1", "t2", "t3"] $ Types.pair
      (Types.function (Types.var "t0") (Types.function Types.int32 (Types.var "t1")))
      (Types.function Types.int32 (Types.function (Types.var "t2") (Types.var "t3"))))

  --Untyped input:
  --	letrecs f = (\x. (\y. (g 0 0)))
  --		g = (\u. (\v. (f v 0)))
  --		in (pair f g)
  --System F type:
  -- 	((Nat -> (Nat -> v12)) * (Nat -> (Nat -> v14)))
  testCase "10"
    ((pair (var "f") (var "g")) `with` [
      "f">: lambda "x" $ lambda "y" (var "g" @@ int32 0 @@ int32 0),
      "g">: lambda "u" $ lambda "v" (var "f" @@ var "v" @@ int32 0)])
    (Types.poly ["t0", "t1"] $ Types.pair
      (Types.function Types.int32 (Types.function Types.int32 (Types.var "t0")))
      (Types.function Types.int32 (Types.function Types.int32 (Types.var "t1"))))

  --Untyped input:
  --	letrecs f = (\x. (\y. (g 0 x)))
  --		g = (\u. (\v. (f 0 0)))
  --		in (pair f g)
  --System F type:
  -- 	((Nat -> (Nat -> v12)) * (Nat -> (Nat -> v14)))
  testCase "11"
    ((pair (var "f") (var "g")) `with` [
      "f">: lambda "x" $ lambda "y" (var "g" @@ int32 0 @@ var "x"),
      "g">: lambda "u" $ lambda "v" (var "f" @@ int32 0 @@ int32 0)])
    (Types.poly ["t0", "t1"] $ Types.pair
      (Types.function Types.int32 (Types.function Types.int32 (Types.var "t0")))
      (Types.function Types.int32 (Types.function Types.int32 (Types.var "t1"))))

expectType :: Term -> TypeScheme -> H.Expectation
expectType term expected = shouldSucceedWith (sInferType term) expected

testCase name term typ = H.it ("test #" ++ name) $ expectType term typ

shouldSucceedWith :: (Eq a, Show a) => Flow SInferenceContext a -> a -> H.Expectation
shouldSucceedWith f x = case my of
    Nothing -> HL.assertFailure "Unknown error" -- TODO: get error message from trace
    Just y -> y `H.shouldBe` x
  where
    FlowState my _ trace = unFlow f sInitialContext Tier1.emptyTrace

spec :: H.Spec
spec = do
  checkAlgorithmW
  checkApplication
  checkLambdas
  checkLists
  checkLambdasAndLists
--  checkPolymorphicRecursion
