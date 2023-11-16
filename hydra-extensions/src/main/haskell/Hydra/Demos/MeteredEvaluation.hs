-- | A small demo of "metered" Hydra evaluation. In this example, the evaluator keeps track of the number of times it
--   calls each primitive function (as a proxy for API calls, which can consume time and resources).

{-# LANGUAGE OverloadedStrings #-}
module Hydra.Demos.MeteredEvaluation (demoMeteredEvaluation) where

import Hydra.Sources.Tier4.All
import Hydra.Dsl.Base as Base
import qualified Hydra.Dsl.Types as Types
import Hydra.Dsl.Lib.Lists as Lists
import Hydra.Dsl.Lib.Strings as Strings
import Hydra.Codegen
import qualified Hydra.Dsl.Lib.Literals as Literals
import qualified Hydra.Dsl.Lib.Math as Math
import qualified Hydra.Dsl.Lib.Strings as Strings

import System.IO
import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import Prelude hiding ((++))


testNs = Namespace "hydra/demos/meteredEvaluation"

testModule :: Module
testModule = Module testNs elements [hydraMantleModule] Nothing
  where
    test local datum = Definition (unqualifyName $ QualifiedName (Just testNs) local) datum
    elements = [
        el $ test "catStrings" (string "foo" ++ string "bar" ++ string "quux" ++ (Literals.showInt32 @@ int32 42)),
        el $ test "describeType" $ ref describeTypeDef @@ (Datum $ coreEncodeType $ Types.list $ Types.int32)]

demoMeteredEvaluation :: IO ()
demoMeteredEvaluation = do
    let state = unFlow evaluateSelectedTerm context emptyTrace
    putStrLn $ traceSummary (flowStateTrace state)
    let result = flowStateValue state
    putStrLn $ "result: " <> show result
  where
    context = modulesToGraph [testModule]
    evaluateSelectedTerm = do
      original <- elementData <$> (requireElement $ unqualifyName $ QualifiedName (Just testNs) "catStrings")
      reduced <- reduceTerm False M.empty original
      return reduced
