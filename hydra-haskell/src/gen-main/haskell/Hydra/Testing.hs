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

_EvaluationStyle_eager = (Core.FieldName "eager")

_EvaluationStyle_lazy = (Core.FieldName "lazy")

-- | A simple test case with an input and an expected output
data TestCase a = 
  TestCase {
    testCaseDescription :: (Maybe String),
    testCaseEvaluationStyle :: EvaluationStyle,
    testCaseInput :: (Core.Term Core.Kv),
    testCaseOutput :: (Core.Term Core.Kv)}
  deriving (Eq, Ord, Read, Show)

_TestCase = (Core.Name "hydra/testing.TestCase")

_TestCase_description = (Core.FieldName "description")

_TestCase_evaluationStyle = (Core.FieldName "evaluationStyle")

_TestCase_input = (Core.FieldName "input")

_TestCase_output = (Core.FieldName "output")

-- | A collection of test cases with a name and optional description
data TestGroup a = 
  TestGroup {
    testGroupName :: String,
    testGroupDescription :: (Maybe String),
    testGroupSubgroups :: [TestGroup Core.Kv],
    testGroupCases :: [TestCase Core.Kv]}
  deriving (Eq, Ord, Read, Show)

_TestGroup = (Core.Name "hydra/testing.TestGroup")

_TestGroup_name = (Core.FieldName "name")

_TestGroup_description = (Core.FieldName "description")

_TestGroup_subgroups = (Core.FieldName "subgroups")

_TestGroup_cases = (Core.FieldName "cases")
