module Hydra.Dsl.Tests (
    module Hydra.Testing,
    module Hydra.Sources.Libraries,
    module Hydra.Dsl.Terms,
    module Hydra.Dsl.Tests,
) where

import Hydra.Core
import Hydra.Testing
import Hydra.Sources.Libraries
import Hydra.Dsl.Terms

import qualified Data.List as L
import qualified Data.Set as S


intList :: [Int] -> Term Kv
intList els = list (int32 <$> els)

intListList :: [[Int]] -> Term Kv
intListList lists = list (intList <$> lists)

primCase :: Name -> [Term Kv] -> Term Kv -> TestCase Kv
primCase name args output = TestCase Nothing EvaluationStyleEager input output
  where
    input = L.foldl (\a arg -> a @@ arg) (primitive name) args

stringList :: [String] -> Term Kv
stringList els = list (string <$> els)

stringSet :: S.Set String -> Term Kv
stringSet strings = set $ S.fromList $ string <$> S.toList strings

testCase = TestCase Nothing
