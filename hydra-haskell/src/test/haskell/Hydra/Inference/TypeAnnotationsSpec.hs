{-# LANGUAGE OverloadedStrings #-}

module Hydra.Inference.TypeAnnotationsSpec where

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
import Hydra.Inference.InferenceTestUtils

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad


-- Check inference without unification or top-level normalization
checkRawInference :: H.SpecWith ()
checkRawInference = check "raw inference" $ do
  H.describe "Lambdas" $ do
    H.describe "test #1" $ do
      H.it "Raw" $
        expectRawType
          (lambda "x" $ var "x")
          (Types.lambda "tv_0" $ Types.function (Types.var "tv_0") (Types.var "tv_0"))
      H.it "Unified and normalized" $
        expectType
          (lambda "x" $ var "x")
          (Types.lambda "t0" $ Types.function (Types.var "t0") (Types.var "t0"))
    H.describe "test #2" $ do
      H.it "Raw" $
        expectRawType
          ((var "id" @@ (list [var "id" @@ int32 42])) `with` [
            "id">: lambda "x" $ var "x"])
          (Types.var "tv_6")
      H.it "Unified and normalized" $
        expectType
          ((var "id" @@ (list [var "id" @@ int32 42])) `with` [
            "id">: lambda "x" $ var "x"])
          (Types.list Types.int32)

checkTypeAnnotations :: H.SpecWith ()
checkTypeAnnotations = check "type annotations on terms and subterms" $ do

  H.it "Literals" $
    QC.property $ \l -> do
      let term = TermLiteral l
      let term1 = executeFlow (inferTermType term)
      checkType term1 (Types.literal $ literalType l)

  H.it "Lists of literals" $
    QC.property $ \l -> do
      let term = TermList [TermLiteral l]
      let term1 = executeFlow (inferTermType term)
      checkType term1 (Types.list $ Types.literal $ literalType l)
      let (TermTyped (TypedTerm _ (TermList [term2]))) = term1
      checkType term2 (Types.literal $ literalType l)

checkSubtermAnnotations :: H.SpecWith ()
checkSubtermAnnotations = check "additional subterm annotations" $ do

    H.it "Literals" $
      expectTypeAnnotation pure
        (string "foo")
        (Types.string)

    H.describe "Monotyped lists" $ do
      H.it "test #1" $
        expectTypeAnnotation pure
          (list [string "foo"])
          (Types.list Types.string)
      H.it "test #2" $
        expectTypeAnnotation Expect.listHead
          (list [string "foo"])
          Types.string

    H.describe "Monotyped lists within lambdas" $ do
      H.it "test #1" $
        expectTypeAnnotation pure
          (lambda "x" $ list [var "x", string "foo"])
          (Types.function Types.string (Types.list Types.string))
      H.it "test #2" $
        expectTypeAnnotation (Expect.lambdaBody >=> Expect.listHead)
          (lambda "x" $ list [var "x", string "foo"])
          Types.string

    H.describe "Injections" $ do
      H.it "test #1" $
        expectTypeAnnotation pure
          (inject testTypeTimestampName $ Field (FieldName "date") $ string "2023-05-11")
          (TypeVariable testTypeTimestampName)
      H.it "test #2" $
        expectTypeAnnotation pure
          (lambda "ignored" $ (inject testTypeTimestampName $ Field (FieldName "date") $ string "2023-05-11"))
          (Types.lambda "t0" $ Types.function (Types.var "t0") (TypeVariable testTypeTimestampName))

    H.it "Projections" $ do
      expectTypeAnnotation pure
        (project testTypePersonName $ FieldName "firstName")
        (Types.function (TypeVariable testTypePersonName) Types.string)

    H.describe "Case statements" $ do
      H.it "test #1" $
        expectTypeAnnotation pure
          (match testTypeNumberName (Just $ string "it's something else") [
            Field (FieldName "int") $ constant $ string "it's an integer"])
          (Types.function (TypeVariable testTypeNumberName) Types.string)
      H.describe "test #2" $ do
        let  testCase = match testTypeNumberName Nothing [
                          Field (FieldName "int") $ constant $ string "it's an integer",
                          Field (FieldName "float") $ constant $ string "it's a float"]
        H.it "condition #1" $
          expectTypeAnnotation pure testCase
            (Types.function (TypeVariable testTypeNumberName) Types.string)
        H.it "condition #2" $
          expectTypeAnnotation (Expect.casesCase testTypeNumberName "int" >=> (pure . fieldTerm)) testCase
            (Types.function Types.int32 Types.string)

    H.describe "Optional eliminations" $ do
      H.describe "test #1" $ do
        let testCase = matchOpt
                         (string "nothing")
                         (lambda "ignored" $ string "just")
        H.it "condition #1" $
          expectTypeAnnotation pure testCase
            (Types.lambda "t0" $ Types.function (Types.optional $ Types.var "t0") Types.string)
        H.it "condition #2" $
          expectTypeAnnotation Expect.optCasesNothing testCase
            Types.string
        H.it "condition #3" $
          expectTypeAnnotation Expect.optCasesJust testCase
            (Types.lambda "t0" $ Types.function (Types.var "t0") Types.string)
      H.describe "test #2" $ do
        let testCase = lambda "getOpt" $ lambda "x" $
                         (matchOpt
                           (string "nothing")
                           (lambda "_" $ string "just")) @@ (var "getOpt" @@ var "x")
        let getOptType = (Types.function (Types.var "t0") (Types.optional $ Types.var "t1"))
        let constStringType = Types.function (Types.var "t0") Types.string
        H.it "condition #1" $
          expectTypeAnnotation pure testCase
            (Types.lambdas ["t0", "t1"] $ Types.function getOptType constStringType)
        H.it "condition #2" $
          expectTypeAnnotation Expect.lambdaBody testCase
            (Types.lambda "t0" $ constStringType)

    H.describe "Unannotated 'let' terms" $ do
      H.describe "test #1" $ do
        let testCase = lambda "i" $
                         (Terms.primitive _strings_cat @@ list [string "foo", var "i", string "bar"])
                         `with` [
                           "foo">: string "FOO",
                           "bar">: string "BAR"]
        H.it "condition #1" $
          expectTypeAnnotation pure testCase
            (Types.function Types.string Types.string)
        H.it "condition #2" $
          expectTypeAnnotation Expect.lambdaBody testCase
            Types.string
      H.describe "test #2" $ do
        let testCase = lambda "original" $
                         var "alias" `with` [
                           "alias">: var "original"]
        H.it "condition #1" $
          expectTypeAnnotation pure testCase
            (Types.lambda "t0" $ Types.function (Types.var "t0") (Types.var "t0"))
        H.it "condition #2" $
          expectTypeAnnotation Expect.lambdaBody testCase
            (Types.lambda "t0" $ Types.var "t0")
        H.it "condition #3" $
          expectTypeAnnotation (Expect.lambdaBody >=> Expect.letBinding "alias") testCase
            (Types.lambda "t0" $ Types.var "t0")
      H.describe "test #3" $ do
        let testCase = lambda "fun" $ lambda "t" $
                         ((var "funAlias" @@ var "t") `with` [
                           "funAlias">: var "fun"])
        let funType = Types.function (Types.var "t0") (Types.var "t1")
        H.it "condition #1" $
          expectTypeAnnotation pure testCase
            (Types.lambdas ["t0", "t1"] $ Types.function funType funType)
        H.it "condition #2" $
          expectTypeAnnotation (Expect.lambdaBody >=> Expect.lambdaBody) testCase
            (Types.lambda "t1" $ Types.var "t1")
        H.it "condition #3" $
          expectTypeAnnotation (Expect.lambdaBody >=> Expect.lambdaBody >=> Expect.letBinding "funAlias") testCase
            (Types.lambdas ["t0", "t1"] funType)
  where
    tmp term = shouldSucceedWith flow ()
      where
        flow = do
          iterm <- inferTermType term
          fail $ "iterm: " ++ show iterm

checkTyped :: H.SpecWith ()
checkTyped = check "type-annotated terms" $ do

  H.describe "Monomorphic typed terms" $ do
    H.it "test #1" $
      expectType
        (typed Types.string $ string "foo")
        Types.string
    H.it "test #2" $
      expectType
        (pair (typed Types.string $ string "foo") (int32 42))
        (Types.pair Types.string Types.int32)

  H.describe "Polymorphic typed terms" $ do
     H.it "test #1" $
        expectType
          (typed (Types.lambda "t0" $ Types.function (Types.var "t0") (Types.var "t0")) $ lambda "x" $ var "x")
          (Types.lambda "t0" $ Types.function (Types.var "t0") (Types.var "t0"))
     H.it "test #2" $
        expectType
          (typed (Types.lambda "a" $ Types.function (Types.var "a") (Types.var "a")) $ lambda "x" $ var "x")
          (Types.lambda "t0" $ Types.function (Types.var "t0") (Types.var "t0"))

  H.describe "Check that incorrectly typed terms fail" $ do
    H.it "test #1" $
      expectFailure $ typed
        (Types.int32)
        (string "foo")
    H.it "test #2" $
      expectFailure $ typed
        (Types.pair Types.string Types.int32)
        (string "foo")
    H.it "test #3" $
      expectFailure $ typed
        (Types.pair Types.string Types.int32)
        (pair (string "foo") (string "bar"))
    H.it "test #4" $
      expectFailure $ typed
        (Types.lambda "a" $ Types.function (Types.var "a") (Types.var "a"))
        (var "x")

  H.describe "Borderline cases for which type inference arguably should fail, but does not" $ do
    H.it "test #5" $
      expectType
        (typed
          (Types.lambda "a" $ Types.function (Types.var "a") (Types.var "a"))
          (lambda "x" $ int32 42))
        (Types.function Types.int32 Types.int32)
    H.it "test #6" $
      expectType
        (typed
          (Types.lambda "a" $ Types.var "a")
          (lambda "x" $ var "x"))
        (Types.lambda "t0" $ Types.function (Types.var "t0") (Types.var "t0"))
    H.it "test #7" $
      expectType
        (typed
          (Types.lambda "a" $ Types.function (Types.var "a") (Types.var "b"))
          (lambda "x" $ var "x"))
        (Types.lambda "t0" $ Types.function (Types.var "t0") (Types.var "t0"))

--checkTypedTerms :: H.SpecWith ()
--checkTypedTerms = H.describe "Check that term/type pairs are consistent with type inference" $ do
--
--    H.it "Arbitrary typed terms" $
--      QC.property $ \(TypedTerm typ term) -> expectType term typ

checkUserProvidedTypes :: H.SpecWith ()
checkUserProvidedTypes = check "user-provided type annotations" $ do

    H.describe "Top-level type annotations" $ do
      H.it "test #1" $
        expectPolytype
          pretypedEmptyList
          ["p"] (Types.list $ Types.var "p")
      H.it "test #2" $
        expectPolytype
          pretypedEmptyMap
          ["k", "v"] (Types.map (Types.var "k") (Types.var "v"))

    H.describe "Type annotations on let-bound terms" $ do
      H.it "test #1" $
        expectPolytype
          (TermLet $ Let [Field (FieldName "x") pretypedEmptyList] $ var "x")
          ["p"] (Types.list $ Types.var "p")
      H.it "test #2" $
        expectPolytype
          (TermLet $ Let [Field (FieldName "y") pretypedEmptyMap] $ var "y")
          ["k", "v"] (Types.map (Types.var "k") (Types.var "v"))
      H.it "test #3" $
        expectPolytype
          (TermLet $ Let [
            Field (FieldName "x") pretypedEmptyList,
            Field (FieldName "y") pretypedEmptyMap] $ Terms.pair (var "x") (var "y"))
          ["p", "k", "v"] (Types.pair (Types.list $ Types.var "p") (Types.map (Types.var "k") (Types.var "v")))

    H.describe "Check that type variables in subterm annotations are also preserved" $ do
      H.it "test #1" $
        expectPolytype
          (typed (Types.function (Types.var "a") (Types.var "a")) $ lambda "x" $ var "x")
          ["a"] (Types.function (Types.var "a") (Types.var "a"))
      H.it "test #2" $
        expectPolytype
          (typed (Types.lambda "a" $ Types.function (Types.var "a") (Types.var "a")) $ lambda "x" $ var "x")
          ["a"] (Types.function (Types.var "a") (Types.var "a"))
      H.it "test #3" $
        expectPolytype
          (lambda "x" $ typed (Types.var "a") $ var "x")
          ["a"] (Types.function (Types.var "a") (Types.var "a"))
  where
    pretypedEmptyList = typed (Types.list $ Types.var "p") $ list []
    pretypedEmptyMap = typed (Types.map (Types.var "k") (Types.var "v")) $ TermMap M.empty

spec :: H.Spec
spec = do
  checkRawInference
  checkSubtermAnnotations
  checkTypeAnnotations
  checkTyped

--  checkTypedTerms -- (excluded for now)
--  checkUserProvidedTypes -- disabled for now; user-provided type variables are replaced with fresh variables
  return ()
