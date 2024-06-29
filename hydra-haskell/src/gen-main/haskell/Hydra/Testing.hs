-- | A model for unit testing

module Hydra.Testing where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | One of two evaluation styles: eager or lazy
data EvaluationStyle = 
  EvaluationStyleEager  |
  EvaluationStyleLazy 
  deriving (Eq, Ord, Read, Show)

_EvaluationStyle = (Core.Name "hydra/testing.EvaluationStyle")

_EvaluationStyle_eager = (Core.Name "eager")

_EvaluationStyle_lazy = (Core.Name "lazy")

-- | A simple test case with an input and an expected output
data TestCase = 
  TestCase {
    testCaseDescription :: (Maybe String),
    testCaseEvaluationStyle :: EvaluationStyle,
    testCaseInput :: Core.Term,
    testCaseOutput :: Core.Term}
  deriving (Eq, Ord, Read, Show)

_TestCase = (Core.Name "hydra/testing.TestCase")

_TestCase_description = (Core.Name "description")

_TestCase_evaluationStyle = (Core.Name "evaluationStyle")

_TestCase_input = (Core.Name "input")

_TestCase_output = (Core.Name "output")

-- | A collection of test cases with a name and optional description
data TestGroup = 
  TestGroup {
    testGroupName :: String,
    testGroupDescription :: (Maybe String),
    testGroupSubgroups :: [TestGroup],
    testGroupCases :: [TestCase]}
  deriving (Eq, Ord, Read, Show)

_TestGroup = (Core.Name "hydra/testing.TestGroup")

_TestGroup_name = (Core.Name "name")

_TestGroup_description = (Core.Name "description")

_TestGroup_subgroups = (Core.Name "subgroups")

_TestGroup_cases = (Core.Name "cases")
