-- | Test cases for primitive functions

module Hydra.Test.TestSuite where

import qualified Hydra.Compute as Compute
import qualified Hydra.Core as Core
import qualified Hydra.Testing as Testing
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

allTests :: (Testing.TestGroup Compute.Kv)
allTests = Testing.TestGroup {
  Testing.testGroupName = "All tests",
  Testing.testGroupDescription = Nothing,
  Testing.testGroupSubgroups = [
    Testing.TestGroup {
      Testing.testGroupName = "hydra/lib/lists primitives",
      Testing.testGroupDescription = Nothing,
      Testing.testGroupSubgroups = [
        Testing.TestGroup {
          Testing.testGroupName = "apply",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.apply"))),
                  Core.applicationArgument = (Core.TermList [
                    Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.toUpper")),
                    (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.toLower")))])})),
                Core.applicationArgument = (Core.TermList [
                  Core.TermLiteral (Core.LiteralString "One"),
                  Core.TermLiteral (Core.LiteralString "Two"),
                  (Core.TermLiteral (Core.LiteralString "Three"))])})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString "ONE"),
                Core.TermLiteral (Core.LiteralString "TWO"),
                Core.TermLiteral (Core.LiteralString "THREE"),
                Core.TermLiteral (Core.LiteralString "one"),
                Core.TermLiteral (Core.LiteralString "two"),
                (Core.TermLiteral (Core.LiteralString "three"))])}]},
        Testing.TestGroup {
          Testing.testGroupName = "bind",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.bind"))),
                  Core.applicationArgument = (Core.TermList [
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)),
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 2)),
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)),
                    (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 4)))])})),
                Core.applicationArgument = (Core.TermFunction (Core.FunctionLambda (Core.Lambda {
                  Core.lambdaParameter = (Core.Name "x"),
                  Core.lambdaBody = (Core.TermApplication (Core.Application {
                    Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.pure"))),
                    Core.applicationArgument = (Core.TermApplication (Core.Application {
                      Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/math.neg"))),
                      Core.applicationArgument = (Core.TermVariable (Core.Name "x"))}))}))})))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 (0-1))),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 (0-2))),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 (0-3))),
                (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 (0-4))))])}]},
        Testing.TestGroup {
          Testing.testGroupName = "concat",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.concat"))),
                Core.applicationArgument = (Core.TermList [
                  Core.TermList [
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)),
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 2)),
                    (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)))],
                  Core.TermList [
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 4)),
                    (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 5)))],
                  (Core.TermList [
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 6)),
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 7)),
                    (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 8)))])])})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 2)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 4)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 5)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 6)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 7)),
                (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 8)))])}]},
        Testing.TestGroup {
          Testing.testGroupName = "head",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.head"))),
                Core.applicationArgument = (Core.TermList [
                  Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)),
                  Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 2)),
                  (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)))])})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)))}]},
        Testing.TestGroup {
          Testing.testGroupName = "intercalate",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.intercalate"))),
                  Core.applicationArgument = (Core.TermList [
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 0)),
                    (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 0)))])})),
                Core.applicationArgument = (Core.TermList [
                  Core.TermList [
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)),
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 2)),
                    (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)))],
                  Core.TermList [
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 4)),
                    (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 5)))],
                  (Core.TermList [
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 6)),
                    Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 7)),
                    (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 8)))])])})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 2)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 0)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 0)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 4)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 5)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 0)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 0)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 6)),
                Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 7)),
                (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 8)))])}]},
        Testing.TestGroup {
          Testing.testGroupName = "intersperse",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.intersperse"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "and"))})),
                Core.applicationArgument = (Core.TermList [
                  Core.TermLiteral (Core.LiteralString "one"),
                  Core.TermLiteral (Core.LiteralString "two"),
                  (Core.TermLiteral (Core.LiteralString "three"))])})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString "one"),
                Core.TermLiteral (Core.LiteralString "and"),
                Core.TermLiteral (Core.LiteralString "two"),
                Core.TermLiteral (Core.LiteralString "and"),
                (Core.TermLiteral (Core.LiteralString "three"))])}]},
        Testing.TestGroup {
          Testing.testGroupName = "last",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.last"))),
                Core.applicationArgument = (Core.TermList [
                  Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)),
                  Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 2)),
                  (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)))])})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)))}]},
        Testing.TestGroup {
          Testing.testGroupName = "length",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.length"))),
                Core.applicationArgument = (Core.TermList [
                  Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)),
                  Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 2)),
                  (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)))])})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)))}]},
        Testing.TestGroup {
          Testing.testGroupName = "map",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.map"))),
                  Core.applicationArgument = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.toUpper")))})),
                Core.applicationArgument = (Core.TermList [
                  Core.TermLiteral (Core.LiteralString "one"),
                  (Core.TermLiteral (Core.LiteralString "two"))])})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString "ONE"),
                (Core.TermLiteral (Core.LiteralString "TWO"))])}]},
        Testing.TestGroup {
          Testing.testGroupName = "pure",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/lists.pure"))),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "one"))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString "one")])}]}],
      Testing.testGroupCases = []},
    Testing.TestGroup {
      Testing.testGroupName = "hydra/lib/strings primitives",
      Testing.testGroupDescription = Nothing,
      Testing.testGroupSubgroups = [
        Testing.TestGroup {
          Testing.testGroupName = "cat",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.cat"))),
                Core.applicationArgument = (Core.TermList [
                  Core.TermLiteral (Core.LiteralString "one"),
                  Core.TermLiteral (Core.LiteralString "two"),
                  (Core.TermLiteral (Core.LiteralString "three"))])})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralString "onetwothree"))},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.cat"))),
                Core.applicationArgument = (Core.TermList [
                  Core.TermLiteral (Core.LiteralString ""),
                  Core.TermLiteral (Core.LiteralString "one"),
                  Core.TermLiteral (Core.LiteralString ""),
                  (Core.TermLiteral (Core.LiteralString ""))])})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralString "one"))},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.cat"))),
                Core.applicationArgument = (Core.TermList [])})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralString ""))}]},
        Testing.TestGroup {
          Testing.testGroupName = "length",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.length"))),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString ""))})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 0)))},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.length"))),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "a"))})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 1)))},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.length"))),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "one"))})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralInteger (Core.IntegerValueInt32 3)))}]},
        Testing.TestGroup {
          Testing.testGroupName = "splitOn",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "ss"))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "Mississippi"))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString "Mi"),
                Core.TermLiteral (Core.LiteralString "i"),
                (Core.TermLiteral (Core.LiteralString "ippi"))])},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "Mississippi"))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "Mississippi"))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString ""),
                (Core.TermLiteral (Core.LiteralString ""))])},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString " "))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "one two three"))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString "one"),
                Core.TermLiteral (Core.LiteralString "two"),
                (Core.TermLiteral (Core.LiteralString "three"))])},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString " "))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString " one two three "))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString ""),
                Core.TermLiteral (Core.LiteralString "one"),
                Core.TermLiteral (Core.LiteralString "two"),
                Core.TermLiteral (Core.LiteralString "three"),
                (Core.TermLiteral (Core.LiteralString ""))])},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString " "))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "  one two three"))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString ""),
                Core.TermLiteral (Core.LiteralString ""),
                Core.TermLiteral (Core.LiteralString "one"),
                Core.TermLiteral (Core.LiteralString "two"),
                (Core.TermLiteral (Core.LiteralString "three"))])},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "  "))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "  one two three"))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString ""),
                (Core.TermLiteral (Core.LiteralString "one two three"))])},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "aa"))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "aaa"))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString ""),
                (Core.TermLiteral (Core.LiteralString "a"))])},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "a"))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString ""))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString "")])},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString ""))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "abc"))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString ""),
                Core.TermLiteral (Core.LiteralString "a"),
                Core.TermLiteral (Core.LiteralString "b"),
                (Core.TermLiteral (Core.LiteralString "c"))])},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermApplication (Core.Application {
                  Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.splitOn"))),
                  Core.applicationArgument = (Core.TermLiteral (Core.LiteralString ""))})),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString ""))})),
              Testing.testCaseOutput = (Core.TermList [
                Core.TermLiteral (Core.LiteralString "")])}]},
        Testing.TestGroup {
          Testing.testGroupName = "toLower",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.toLower"))),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "One TWO threE"))})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralString "one two three"))},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.toLower"))),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "Abc123"))})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralString "abc123"))}]},
        Testing.TestGroup {
          Testing.testGroupName = "toUpper",
          Testing.testGroupDescription = Nothing,
          Testing.testGroupSubgroups = [],
          Testing.testGroupCases = [
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.toUpper"))),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "One TWO threE"))})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralString "ONE TWO THREE"))},
            Testing.TestCase {
              Testing.testCaseDescription = Nothing,
              Testing.testCaseEvaluationStyle = Testing.EvaluationStyleEager,
              Testing.testCaseInput = (Core.TermApplication (Core.Application {
                Core.applicationFunction = (Core.TermFunction (Core.FunctionPrimitive (Core.Name "hydra/lib/strings.toUpper"))),
                Core.applicationArgument = (Core.TermLiteral (Core.LiteralString "Abc123"))})),
              Testing.testCaseOutput = (Core.TermLiteral (Core.LiteralString "ABC123"))}]}],
      Testing.testGroupCases = []}],
  Testing.testGroupCases = []}