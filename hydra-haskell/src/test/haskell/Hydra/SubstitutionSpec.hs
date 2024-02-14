{-# LANGUAGE OverloadedStrings #-}

module Hydra.SubstitutionSpec where

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
import Hydra.Substitution

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad


checkInstantiation :: H.SpecWith ()
checkInstantiation = H.describe "Check type instantiation" $ do

  H.describe "Lambdas" $ do
    H.it "test #1" $ shouldSucceedWith
      (instantiate $ Types.lambda "x" $ Types.var "x")
      (Types.lambda "tv_0" $ Types.var "tv_0")
    H.it "test #2" $ shouldSucceedWith
      (instantiate $ Types.lambda "x" $ Types.list $ Types.var "x")
      (Types.lambda "tv_0" $ Types.list $ Types.var "tv_0")

spec :: H.Spec
spec = do
  checkInstantiation
