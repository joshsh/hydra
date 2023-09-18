module Hydra.Sources.Tier4.Test.Lib.Strings (stringPrimitiveTests) where

import Hydra.Dsl.Tests


stringPrimitiveTests :: TestGroup
stringPrimitiveTests = TestGroup "hydra/lib/strings primitives" Nothing groups []
  where
    groups = [stringsCat, stringsLength, stringsSplitOn, stringsToLower, stringsToUpper]

stringsCat :: TestGroup
stringsCat = TestGroup "cat" Nothing [] [
    test ["one", "two", "three"] "onetwothree",
    test ["", "one", "", ""] "one",
    test [] ""]
  where
    test ls result = primCase _strings_cat [list (string <$> ls)] (string result)

stringsLength :: TestGroup
stringsLength = TestGroup "length" Nothing [] [
    test "" 0,
    test "a" 1,
    test "one" 3]
  where
    test s result = primCase _strings_length [string s] (int32 result)

stringsSplitOn :: TestGroup
stringsSplitOn = TestGroup "splitOn" Nothing [] [
    test "ss" "Mississippi" ["Mi", "i", "ippi"],
    test "Mississippi" "Mississippi" ["", ""],

    test " " "one two three" ["one", "two", "three"],
    test " " " one two three " ["", "one", "two", "three", ""],
    test " " "  one two three" ["", "", "one", "two", "three"],
    test "  " "  one two three" ["", "one two three"],

    test "aa" "aaa" ["", "a"],

    test "a" "" [""],

    test "" "abc" ["", "a", "b", "c"],
    test "" "" [""]]
  where
    test s0 s1 result = primCase _strings_splitOn [string s0, string s1] (list (string <$> result))

stringsToLower :: TestGroup
stringsToLower = TestGroup "toLower" Nothing [] [
    test "One TWO threE" "one two three",
    test "Abc123" "abc123"]
  where
    test s result = primCase _strings_toLower [string s] (string result)

stringsToUpper :: TestGroup
stringsToUpper = TestGroup "toUpper" Nothing [] [
    test "One TWO threE" "ONE TWO THREE",
    test "Abc123" "ABC123"]
  where
    test s result = primCase _strings_toUpper [string s] (string result)
