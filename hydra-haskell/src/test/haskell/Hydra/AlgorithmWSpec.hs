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

checkAll :: H.SpecWith ()
checkAll = H.describe "All test cases" $ do
  H.it "#0" $ expectType
    (string "foo")
    Types.string
--  H.it "#1" $ expectType
--    (lambda "x" $ var "x")
--    (Types.lambda "v1" $ Types.function (Types.var "v1") (Types.var "v1"))

spec :: H.Spec
spec = do
  checkAll
