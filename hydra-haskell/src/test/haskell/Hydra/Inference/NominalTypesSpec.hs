{-# LANGUAGE OverloadedStrings #-}

module Hydra.Inference.NominalTypesSpec where

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
import Hydra.TestUtils
import Hydra.Inference.InferenceTestUtils

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad


checkCaseStatements :: H.SpecWith ()
checkCaseStatements = check "case statements (variant eliminations)" $ do

  H.it "test #1" $ do
    expectType
      (match testTypeSimpleNumberName Nothing [
        Field (Name "int") $ lambda "x" $ var "x",
        Field (Name "float") $ lambda "x" $ int32 42])
      (funT (TypeVariable testTypeSimpleNumberName) Types.int32)

  H.it "test #2" $ do
    expectType
      (match testTypeUnionMonomorphicName Nothing [
        Field (Name "bool") (lambda "x" (boolean True)),
        Field (Name "string") (lambda "x" (boolean False)),
        Field (Name "unit") (lambda "x" (boolean False))])
      (Types.function (TypeVariable testTypeUnionMonomorphicName) Types.boolean)

checkProjections :: H.SpecWith ()
checkProjections = check "projections (record eliminations)" $ do

  H.it "Projections" $ do
    expectType
      (project testTypePersonName (Name "firstName"))
      (Types.function (TypeVariable testTypePersonName) Types.string)

checkRecords :: H.SpecWith ()
checkRecords = check "records" $ do

  H.describe "Simple records" $ do
    H.it "test #1" $
      expectType
        (record testTypeLatLonName [
          Field (Name "lat") $ float32 37.7749,
          Field (Name "lon") $ float32 $ negate 122.4194])
        (TypeVariable testTypeLatLonName)
    H.it "test #2" $
      expectType
        (record testTypeLatLonPolyName [
          Field (Name "lat") $ float32 37.7749,
          Field (Name "lon") $ float32 $ negate 122.4194])
        (Types.apply (TypeVariable testTypeLatLonPolyName) Types.float32)
    H.it "test #3" $
      expectType
        (lambda "lon" (record testTypeLatLonPolyName [
          Field (Name "lat") $ float32 37.7749,
          Field (Name "lon") $ var "lon"]))
        (Types.function (Types.float32) (Types.apply (TypeVariable testTypeLatLonPolyName) Types.float32))
    H.it "test #4" $
      expectPolytype
        (lambda "latlon" (record testTypeLatLonPolyName [
          Field (Name "lat") $ var "latlon",
          Field (Name "lon") $ var "latlon"]))
        ["t0"] (Types.function (Types.var "t0") (Types.apply (TypeVariable testTypeLatLonPolyName) (Types.var "t0")))
    H.it "test #5" $
      expectType
        testDataArthur
        (TypeVariable testTypePersonName)

  H.describe "Record instances of simply recursive record types" $ do
    H.it "test #1" $
      expectType
        (record testTypeIntListName [
          Field (Name "head") $ int32 42,
          Field (Name "tail") $ optional $ Just $ record testTypeIntListName [
            Field (Name "head") $ int32 43,
            Field (Name "tail") $ optional Nothing]])
        (TypeVariable testTypeIntListName)
    H.it "test #2" $
      expectType
        ((lambda "x" $ record testTypeIntListName [
          Field (Name "head") $ var "x",
          Field (Name "tail") $ optional $ Just $ record testTypeIntListName [
            Field (Name "head") $ var "x",
            Field (Name "tail") $ optional Nothing]]) @@ int32 42)
        (TypeVariable testTypeIntListName)
    H.it "test #3" $
      expectType
        (record testTypeListName [
          Field (Name "head") $ int32 42,
          Field (Name "tail") $ optional $ Just $ record testTypeListName [
            Field (Name "head") $ int32 43,
            Field (Name "tail") $ optional Nothing]])
        (Types.apply (TypeVariable testTypeListName) Types.int32)
    H.it "test #4" $
      expectType
        ((lambda "x" $ record testTypeListName [
          Field (Name "head") $ var "x",
          Field (Name "tail") $ optional $ Just $ record testTypeListName [
            Field (Name "head") $ var "x",
            Field (Name "tail") $ optional Nothing]]) @@ int32 42)
        (Types.apply (TypeVariable testTypeListName) Types.int32)
    H.it "test #5" $
      expectPolytype
        (lambda "x" $ record testTypeListName [
          Field (Name "head") $ var "x",
          Field (Name "tail") $ optional $ Just $ record testTypeListName [
            Field (Name "head") $ var "x",
            Field (Name "tail") $ optional Nothing]])
        ["t0"] (Types.function (Types.var "t0") (Types.apply (TypeVariable testTypeListName) (Types.var "t0")))

  H.describe "Record instances of mutually recursive record types" $ do
    H.it "test #1" $
      expectType
        ((lambda "x" $ record testTypeBuddyListAName [
          Field (Name "head") $ var "x",
          Field (Name "tail") $ optional $ Just $ record testTypeBuddyListBName [
            Field (Name "head") $ var "x",
            Field (Name "tail") $ optional Nothing]]) @@ int32 42)
        (Types.apply (TypeVariable testTypeBuddyListAName) Types.int32)
    H.it "test #2" $
      expectPolytype
        (lambda "x" $ record testTypeBuddyListAName [
          Field (Name "head") $ var "x",
          Field (Name "tail") $ optional $ Just $ record testTypeBuddyListBName [
            Field (Name "head") $ var "x",
            Field (Name "tail") $ optional Nothing]])
        ["t0"] (Types.function (Types.var "t0") (Types.apply (TypeVariable testTypeBuddyListAName) (Types.var "t0")))

checkTypeDefinitions :: H.SpecWith ()
checkTypeDefinitions = check "type definition terms" $ do

  unit <- pure $ string "ignored"
  H.describe "Approximation of Hydra type definitions" $ do
    H.it "test #1.a" $
      expectType
        (variant testTypeHydraTypeName (Name "literal")
          $ variant testTypeHydraLiteralTypeName (Name "boolean") unit)
        (TypeVariable testTypeHydraTypeName)
    H.it "test #1.b" $
      expectFailure
        (variant testTypeHydraTypeName (Name "literal")
          $ variant testTypeHydraLiteralTypeName (Name "boolean") $ int32 42)
    H.it "test #2.a" $
      expectType
        ((variant testTypeHydraTypeName (Name "list") $ var "otherType") `with` [
          "otherType">: variant testTypeHydraTypeName (Name "literal")
            $ variant testTypeHydraLiteralTypeName (Name "boolean") unit])
        (TypeVariable testTypeHydraTypeName)
    H.it "test #2.b" $
      expectFailure
        ((variant testTypeHydraTypeName (Name "list") $ var "otherType") `with` [
          "otherType">: variant testTypeHydraTypeName (Name "literal")
            $ variant testTypeHydraLiteralTypeName (Name "boolean") $ int32 42])

checkVariants :: H.SpecWith ()
checkVariants = check "variant terms" $ do

  H.describe "Variants" $ do
    H.it "test #1" $
      expectType
        (inject testTypeTimestampName $ Field (Name "unixTimeMillis") $ uint64 1638200308368)
        (TypeVariable testTypeTimestampName)
    H.it "test #2" $
      expectType
        (inject testTypeUnionMonomorphicName $ Field (Name "string") $ string "bar")
        (TypeVariable testTypeUnionMonomorphicName)
    H.it "test #3" $
      expectFailure
        (inject testTypeUnionMonomorphicName $ Field (Name "string") $ int32 42)

  H.describe "Polymorphic and recursive variants" $ do
    H.it "test #1" $
      expectType
        (variant testTypeUnionPolymorphicRecursiveName (Name "bool") $ boolean True)
        (Types.lambda "t0" $ Types.apply (TypeVariable testTypeUnionPolymorphicRecursiveName) (Types.var "t0"))
    H.it "test #2" $
      expectType
        (variant testTypeUnionPolymorphicRecursiveName (Name "value") $ string "foo")
        (Types.apply (TypeVariable testTypeUnionPolymorphicRecursiveName) Types.string)
    H.it "test #3" $
      expectType
        ((variant testTypeUnionPolymorphicRecursiveName (Name "other") $ var "other") `with` [
          "other">: variant testTypeUnionPolymorphicRecursiveName (Name "value") $ int32 42])
        (Types.apply (TypeVariable testTypeUnionPolymorphicRecursiveName) Types.int32)

checkWrappers :: H.SpecWith ()
checkWrappers = check "wrapper introductions and eliminations" $ do

  H.describe "Wrapper introductions" $ do
    H.it "test #1" $
      expectType
        (wrap testTypeStringAliasName $ string "foo")
        (TypeVariable testTypeStringAliasName)
    H.it "test #2" $
      expectType
        (lambda "v" $ wrap testTypeStringAliasName $ var "v")
        (Types.function Types.string (TypeVariable testTypeStringAliasName))

  H.describe "Wrapper eliminations" $ do
    H.it "test #1" $
      expectType
        (unwrap testTypeStringAliasName)
        (Types.function (TypeVariable testTypeStringAliasName) Types.string)
    H.it "test #2" $
      expectType
        (unwrap testTypeStringAliasName @@ (wrap testTypeStringAliasName $ string "foo"))
        Types.string

spec :: H.Spec
spec = do
  checkCaseStatements
  checkProjections
  checkRecords
  checkTypeDefinitions
  checkVariants
  checkWrappers
