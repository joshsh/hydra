{-# LANGUAGE OverloadedStrings #-}

module Hydra.AlgorithmWSpec where

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
import Hydra.AlgorithmW

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad


expectType :: Term -> Type -> H.Expectation
expectType term typ = H.shouldReturn (snd <$> inferWithAlgorithmW term) typ

-- @wisnesky's original Algorithm W test cases
checkAlgorithmW :: H.SpecWith ()
checkAlgorithmW = H.describe "Check System F syntax" $ do
  --Untyped input:
  --	(\x. x)
  --System F type:
  -- 	(v0 -> v0)
  H.it "#0" $ expectType
    (lambda "x" $ var "x")
    (Types.lambda "v1" $ Types.function (Types.var "v1") (Types.var "v1"))

  --Untyped input:
  --	letrecs foo = (\x. x)
  --		in 42
  --System F type:
  -- 	Nat
  H.it "#1" $ expectType
    (int32 32 `with` [
      "foo">: lambda "x" $ var "x"])
    Types.int32

  --Untyped input:
  --	let f = (\x. x) in (f 0)
  --System F type:
  -- 	Nat
  H.it "#2" $ expectType
    ((var "f" @@ int32 0) `with` [
      "f">: lambda "x" $ var "x"])
    Types.int32

  --Untyped input:
  --	let f = ((\x. x) 0) in f
  --System F type:
  -- 	Nat
  H.it "#3" $ expectType
    (var "f" `with` [
      "f">: (lambda "x" $ var "x") @@ int32 0])
    Types.int32

  --Untyped input:
  --	let sng = (\x. (cons x nil)) in sng
  --System F type:
  -- 	(v5 -> (List v5))
  H.it "#4" $ expectType
    (var "sng" `with` [
      "sng">: lambda "x" $ list [var "x"]])
    (Types.lambda "v7" $ Types.function (Types.var "v7") (Types.list (Types.var "v7")))

  --Untyped input:
  --	let sng = (\x. (cons x nil)) in (pair (sng 0) (sng alice))
  --System F type:
  -- 	((List Nat) * (List String))
  H.it "#5" $ expectType
    (pair (var "sng" @@ int32 0) (var "sng" @@ string "alice") `with` [
      "sng">: lambda "x" $ list [var "x"]])
    (Types.pair (Types.list Types.int32) (Types.list Types.string))

  --Untyped input:
  --	letrecs + = (\x. (\y. (S (+ (P x) y))))
  --		in (+ (S (S 0)) (S 0))
  --System F type:
  -- 	Nat
  H.it "#6" $ expectType
    ((var "+" @@ (primSucc @@ (primSucc @@ int32 0)) @@ (primSucc @@ int32 0)) `with` [
      "+" >: lambda "x" $ lambda "y" (primSucc @@ (var "+" @@ (primPred @@ var "x") @@ var "y"))])
    Types.int32

  --Untyped input:
  --	letrecs f = (\x. (\y. (f 0 x)))
  --		in f
  --System F type:
  -- 	(Nat -> (Nat -> v5))
  H.it "#7" $ expectType
    (var "f" `with` [
      "f">: lambda "x" $ lambda "y" (var "f" @@ int32 0 @@ var "x")])
    (Types.lambda "v6" $ Types.function Types.int32 (Types.function Types.int32 (Types.var "v6")))

  --Untyped input:
  --	letrecs f = (\x. (\y. (g 0 x)))
  --		g = (\u. (\v. (f v 0)))
  --		in (pair f g)
  --System F type:
  -- 	((v12 -> (Nat -> v13)) * (Nat -> (v15 -> v16)))
  H.it "#9" $ expectType
    ((pair (var "f") (var "g")) `with` [
      "f">: lambda "x" $ lambda "y" (var "g" @@ int32 0 @@ var "x"),
      "g">: lambda "u" $ lambda "v" (var "f" @@ var "v" @@ int32 0)])
    (Types.lambdas ["v13", "v14", "v16", "v17"] $ Types.pair
      (Types.function (Types.var "v13") (Types.function Types.int32 (Types.var "v14")))
      (Types.function Types.int32 (Types.function (Types.var "v16") (Types.var "v17"))))

  --Untyped input:
  --	letrecs f = (\x. (\y. (g 0 0)))
  --		g = (\u. (\v. (f v 0)))
  --		in (pair f g)
  --System F type:
  -- 	((Nat -> (Nat -> v12)) * (Nat -> (Nat -> v14)))
  H.it "#10" $ expectType
    ((pair (var "f") (var "g")) `with` [
      "f">: lambda "x" $ lambda "y" (var "g" @@ int32 0 @@ int32 0),
      "g">: lambda "u" $ lambda "v" (var "f" @@ var "v" @@ int32 0)])
    (Types.lambdas ["v13", "v15"] $ Types.pair
      (Types.function Types.int32 (Types.function Types.int32 (Types.var "v13")))
      (Types.function Types.int32 (Types.function Types.int32 (Types.var "v15"))))

  --Untyped input:
  --	letrecs f = (\x. (\y. (g 0 x)))
  --		g = (\u. (\v. (f 0 0)))
  --		in (pair f g)
  --System F type:
  -- 	((Nat -> (Nat -> v12)) * (Nat -> (Nat -> v14)))
  H.it "#11" $ expectType
    ((pair (var "f") (var "g")) `with` [
      "f">: lambda "x" $ lambda "y" (var "g" @@ int32 0 @@ var "x"),
      "g">: lambda "u" $ lambda "v" (var "f" @@ int32 0 @@ int32 0)])
    (Types.lambdas ["v13", "v15"] $ Types.pair
      (Types.function Types.int32 (Types.function Types.int32 (Types.var "v13")))
      (Types.function Types.int32 (Types.function Types.int32 (Types.var "v15"))))

checkOther :: H.SpecWith ()
checkOther = H.describe "All test cases" $ do
  H.it "#0" $ expectType
    (string "foo")
    Types.string
  H.it "#1" $ expectType
    (list [string "foo", string "bar"])
    (Types.list Types.string)

spec :: H.Spec
spec = do
  checkAlgorithmW
  checkOther
