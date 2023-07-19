{-# LANGUAGE OverloadedStrings #-}

module Hydra.InferenceSpec where

import Hydra.Kernel
import Hydra.Sources.Libraries
import Hydra.Inference
import Hydra.TestUtils
import Hydra.TestData
import qualified Hydra.Dsl.Expect as Expect
import Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Annotations as Ann
import qualified Hydra.Dsl.Types as Types

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad


checkType :: Term (Kv, Type Kv, [Constraint Kv]) -> Type Kv -> H.Expectation
checkType term typ = typeAnn term `H.shouldBe` typ
  where
    typeAnn (TermAnnotated (Annotated _ (_, typ, _))) = typ

expectMonotype :: Term Kv -> Type Kv -> H.Expectation
expectMonotype term = expectPolytype term []

expectPolytype :: Term Kv-> [String] -> Type Kv -> H.Expectation
expectPolytype term vars typ = do
    shouldSucceedWith
      (inferTypeScheme term)
      (TypeScheme (Name <$> vars) typ)

expectTypeAnnotation :: (Term Kv -> Flow (Graph Kv) (Term Kv)) -> Term Kv -> Type Kv -> H.Expectation
expectTypeAnnotation path term etyp = shouldSucceedWith atyp etyp
  where
   atyp = do
     iterm <- annotateTermWithTypes term
     selected <- path iterm
     mtyp <- getType (termAnnotationInternal selected)
     case mtyp of
       Nothing -> fail $ "no type annotation"
       Just t -> pure t

checkApplicationTerms :: H.SpecWith ()
checkApplicationTerms = H.describe "Check a few hand-picked application terms" $ do

    H.it "Check lambda applications" $ do
      expectMonotype
        (apply (lambda "x" (var "x")) (string "foo"))
        Types.string

    H.it "Check mixed expressions with lambdas, constants, and primitive functions" $ do
      expectMonotype
        (lambda "x" $
          apply
            (apply (primitive _math_sub) (apply (apply (primitive _math_add) (var "x")) (var "x")))
            (int32 1))
        (Types.function Types.int32 Types.int32)

checkFunctionTerms :: H.SpecWith ()
checkFunctionTerms = H.describe "Check a few hand-picked function terms" $ do

    H.it "Check lambdas" $ do
      expectPolytype
        (lambda "x" (var "x"))
        ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))
      expectPolytype
        (lambda "x" (int16 137))
        ["t0"] (Types.function (Types.var "t0") Types.int16)

    H.it "Check list eliminations" $ do
      let fun = Terms.fold $ primitive _math_add
      expectMonotype
        fun
        (Types.functionN [Types.int32, Types.list Types.int32] Types.int32)
      expectMonotype
        (apply fun $ int32 0)
        (Types.function (Types.list Types.int32) Types.int32)
      expectMonotype
        (apply (apply fun $ int32 0) (list (int32 <$> [1, 2, 3, 4, 5])))
        Types.int32

    H.it "Check projections" $ do
      expectMonotype
        (project testTypePersonName (FieldName "firstName"))
        (Types.function testTypePerson Types.string)

    H.it "Check case statements" $ do
      expectMonotype
        (match testTypeFoobarValueName Nothing [
          Field (FieldName "bool") (lambda "x" (boolean True)),
          Field (FieldName "string") (lambda "x" (boolean False)),
          Field (FieldName "unit") (lambda "x" (boolean False))])
        (Types.function testTypeFoobarValue Types.boolean)

checkIndividualTerms :: H.SpecWith ()
checkIndividualTerms = H.describe "Check a few hand-picked terms" $ do

    H.it "Check literal values" $ do
      expectMonotype
        (int32 42)
        Types.int32
      expectMonotype
        (string "foo")
        Types.string
      expectMonotype
        (boolean False)
        Types.boolean
      expectMonotype
        (float64 42.0)
        Types.float64

    H.it "Check let terms" $ do
      expectPolytype
        (letTerm (Name "x") (float32 42.0) (lambda "y" (lambda "z" (var "x"))))
        ["t0", "t1"] (Types.function (Types.var "t0") (Types.function (Types.var "t1") Types.float32))

    H.it "Check optionals" $ do
      expectMonotype
        (optional $ Just $ int32 42)
        (Types.optional Types.int32)
      expectPolytype
        (optional Nothing)
        ["t0"] (Types.optional $ Types.var "t0")

    H.it "Check records" $ do
      expectMonotype
        (record latLonName [
          Field (FieldName "lat") $ float32 37.7749,
          Field (FieldName "lon") $ float32 $ negate 122.4194])
        (TypeRecord $ RowType latLonName Nothing [
          FieldType (FieldName "lat") Types.float32,
          FieldType (FieldName "lon") Types.float32])
      expectMonotype
        (record latLonPolyName [
          Field (FieldName "lat") $ float32 37.7749,
          Field (FieldName "lon") $ float32 $ negate 122.4194])
        (TypeRecord $ RowType latLonPolyName Nothing [
          FieldType (FieldName "lat") Types.float32,
          FieldType (FieldName "lon") Types.float32])
      expectMonotype
        (lambda "lon" (record latLonPolyName [
          Field (FieldName "lat") $ float32 37.7749,
          Field (FieldName "lon") $ var "lon"]))
        (Types.function (Types.float32)
          (TypeRecord $ RowType latLonPolyName Nothing [
            FieldType (FieldName "lat") $ Types.float32,
            FieldType (FieldName "lon") $ Types.float32]))
      expectPolytype
        (lambda "latlon" (record latLonPolyName [
          Field (FieldName "lat") $ var "latlon",
          Field (FieldName "lon") $ var "latlon"]))
        ["t0"] (Types.function (Types.var "t0")
          (TypeRecord $ RowType latLonPolyName Nothing [
            FieldType (FieldName "lat") $ Types.var "t0",
            FieldType (FieldName "lon") $ Types.var "t0"]))

    H.it "Check unions" $ do
      expectMonotype
        (inject testTypeTimestampName $ Field (FieldName "unixTimeMillis") $ uint64 1638200308368)
        testTypeTimestamp

    H.it "Check sets" $ do
      expectMonotype
        (set $ S.fromList [boolean True])
        (Types.set Types.boolean)
      expectPolytype
        (set $ S.fromList [set S.empty])
        ["t0"] (Types.set $ Types.set $ Types.var "t0")

    H.it "Check maps" $ do
      expectMonotype
        (mapTerm $ M.fromList [(string "firstName", string "Arthur"), (string "lastName", string "Dent")])
        (Types.map Types.string Types.string)
      expectPolytype
        (mapTerm M.empty)
        ["t0", "t1"] (Types.map (Types.var "t0") (Types.var "t1"))
      expectPolytype
        (lambda "x" (lambda "y" (mapTerm $ M.fromList
          [(var "x", float64 0.1), (var "y", float64 0.2)])))
        ["t0"] (Types.function (Types.var "t0") (Types.function (Types.var "t0") (Types.map (Types.var "t0") Types.float64)))

    -- -- TODO: add a case for a recursive nominal type -- e.g. MyList := () + (int, Mylist)
    -- H.it "Check nominal (newtype) terms" $ do
    --   expectMonotype
    --     testDataArthur
    --     (Types.wrap "Person")
    --   expectMonotype
    --     (lambda "x" (record [
    --       Field "firstName" $ var "x",
    --       Field "lastName" $ var "x",
    --       Field "age" $ int32 42]))
    --     (Types.function Types.string testTypePerson)

checkLetTerms :: H.SpecWith ()
checkLetTerms = H.describe "Check a few hand-picked let terms" $ do

    H.it "Check empty let" $ do
      expectMonotype
        ((int32 42) `with` [])
        Types.int32

    H.it "Check trivial let" $ do
      expectMonotype
        (var "foo" `with` [
          "foo">: int32 42])
        Types.int32

checkLists :: H.SpecWith ()
checkLists = H.describe "Check a few hand-picked list terms" $ do

    H.it "Check list of strings" $ do
      expectMonotype
        (list [string "foo", string "bar"])
        (Types.list Types.string)
    H.it "Check list of lists of strings" $ do
      expectMonotype
        (list [list [string "foo"], list []])
        (Types.list $ Types.list Types.string)
    H.it "Check empty list" $ do
      expectPolytype
        (list [])
        ["t0"] (Types.list $ Types.var "t0")
    H.it "Check list containing an empty list" $ do
      expectPolytype
        (list [list []])
        ["t0"] (Types.list $ Types.list $ Types.var "t0")
    H.it "Check lambda producing a list of integers" $ do
      expectMonotype
        (lambda "x" (list [var "x", int32 42]))
        (Types.function Types.int32 $ Types.list Types.int32)
    H.it "Check list with bound variables" $ do
      expectMonotype
        (lambda "x" (list [var "x", string "foo", var "x"]))
        (Types.function Types.string (Types.list Types.string))

checkLiterals :: H.SpecWith ()
checkLiterals = H.describe "Check arbitrary literals" $ do

    H.it "Verify that type inference preserves the literal to literal type mapping" $
      QC.property $ \l -> expectMonotype
        (TermLiteral l)
        (Types.literal $ literalType l)

checkWrappedTerms :: H.SpecWith ()
checkWrappedTerms = H.describe "Check nominal introductions and eliminations" $ do

    H.it "Check nominal introductions" $ do
      expectMonotype
        (wrap stringAliasTypeName $ string "foo")
        stringAliasType
      expectMonotype
        (lambda "v" $ wrap stringAliasTypeName $ var "v")
        (Types.function Types.string stringAliasType)

    H.it "Check nominal eliminations" $ do
--       expectMonotype
--         (unwrap stringAliasTypeName)
--         (Types.function stringAliasType (Ann.doc "An alias for the string type" Types.string))
      expectMonotype
        (apply (unwrap stringAliasTypeName) (wrap stringAliasTypeName $ string "foo"))
        Types.string

checkPrimitives :: H.SpecWith ()
checkPrimitives = H.describe "Check a few hand-picked terms with primitive functions" $ do

    H.it "Check monomorphic primitive functions" $ do
      expectMonotype
        (primitive $ Name "hydra/lib/strings.length")
        (Types.function Types.string Types.int32)
      expectMonotype
        (primitive _math_sub)
        (Types.function Types.int32 (Types.function Types.int32 Types.int32))

    H.it "Check polymorphic primitive functions" $ do
      expectPolytype
        (lambda "els" (apply (primitive _lists_length) (apply (primitive _lists_concat) $ var "els")))
        ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") Types.int32)

checkProducts :: H.SpecWith ()
checkProducts = H.describe "Check a few hand-picked product terms" $ do

    H.it "Check empty product" $ do
      expectMonotype
        (Terms.product [])
        (Types.product [])

    H.it "Check non-empty, monotyped products" $ do
      expectMonotype
        (Terms.product [string "foo", int32 42])
        (Types.product [Types.string, Types.int32])
      expectMonotype
        (Terms.product [string "foo", list [float32 42.0, float32 137.0]])
        (Types.product [Types.string, Types.list Types.float32])

    H.it "Check polytyped products" $ do
      expectPolytype
        (Terms.product [list [], string "foo"])
        ["t0"] (Types.product [Types.list $ Types.var "t0", Types.string])

checkSums :: H.SpecWith ()
checkSums = H.describe "Check a few hand-picked sum terms" $ do

    H.it "Check singleton sum terms" $ do
      expectMonotype
        (Terms.sum 0 1 $ string "foo")
        (Types.sum [Types.string])
      expectPolytype
        (Terms.sum 0 1 $ list [])
        ["t0"] (Types.sum [Types.list $ Types.var "t0"])

    H.it "Check non-singleton sum terms" $ do
      expectPolytype
        (Terms.sum 0 2 $ string "foo")
        ["t0"] (Types.sum [Types.string, Types.var "t0"])
      expectPolytype
        (Terms.sum 1 2 $ string "foo")
        ["t0"] (Types.sum [Types.var "t0", Types.string])

checkTypeAnnotations :: H.SpecWith ()
checkTypeAnnotations = H.describe "Check that type annotations are added to terms and subterms" $ do

    H.it "Check literals" $
      QC.property $ \l -> do
        let term = TermLiteral l
        let term1 = fromFlow testGraph (fst <$> inferTypeAndConstraints term)
        checkType term1 (Types.literal $ literalType l)

    H.it "Check lists of literals" $
      QC.property $ \l -> do
        let term = TermList [TermLiteral l]
        let term1 = fromFlow testGraph (fst <$> inferTypeAndConstraints term)
        checkType term1 (Types.list $ Types.literal $ literalType l)
        let (TermAnnotated (Annotated (TermList [term2]) _)) = term1
        checkType term2 (Types.literal $ literalType l)

checkSubtermAnnotations :: H.SpecWith ()
checkSubtermAnnotations = H.describe "Check additional subterm annotations" $ do

    H.it "Check literals" $
      expectTypeAnnotation pure
        (string "foo")
        (Types.string)

    H.it "Check monotyped lists" $ do
      expectTypeAnnotation pure
        (list [string "foo"])
        (Types.list Types.string)
      expectTypeAnnotation Expect.listHead
        (list [string "foo"])
        Types.string

    H.it "Check monotyped lists within lambdas" $ do
      expectTypeAnnotation pure
        (lambda "x" $ list [var "x", string "foo"])
        (Types.function Types.string (Types.list Types.string))
      expectTypeAnnotation (Expect.lambdaBody >=> Expect.listHead)
        (lambda "x" $ list [var "x", string "foo"])
        Types.string

    H.it "Check injections" $ do
      expectTypeAnnotation pure
        (inject testTypeTimestampName $ Field (FieldName "date") $ string "2023-05-11")
        testTypeTimestamp
      expectTypeAnnotation pure
        (lambda "ignored" $ (inject testTypeTimestampName $ Field (FieldName "date") $ string "2023-05-11"))
        (Types.function (Types.var "t0") testTypeTimestamp)

    H.it "Check projections" $ do
      expectTypeAnnotation pure
        (project testTypePersonName $ FieldName "firstName")
        (Types.function testTypePerson Types.string)

    H.describe "Check case statements" $ do
      H.it "test #1" $ do
        expectTypeAnnotation pure
          (match testTypeNumberName (Just $ string "it's something else") [
            Field (FieldName "int") $ constant $ string "it's an integer"])
          (Types.function testTypeNumber Types.string)
      H.it "test #2" $ do
        let  testCase = match testTypeNumberName Nothing [
                          Field (FieldName "int") $ constant $ string "it's an integer",
                          Field (FieldName "float") $ constant $ string "it's a float"]
        expectTypeAnnotation pure testCase
          (Types.function testTypeNumber Types.string)
        expectTypeAnnotation (Expect.casesCase testTypeNumberName "int" >=> (pure . fieldTerm)) testCase
          (Types.function Types.int32 Types.string)

    H.describe "Check optional eliminations" $ do
      H.it "test #1" $ do
        let testCase = matchOpt
                         (string "nothing")
                         (lambda "ignored" $ string "just")
        expectTypeAnnotation pure testCase
          (Types.function (Types.optional $ Types.var "t2") Types.string)
        expectTypeAnnotation Expect.optCasesNothing testCase
          Types.string
        expectTypeAnnotation Expect.optCasesJust testCase
          (Types.function (Types.var "t2") Types.string)
      H.it "test #2" $ do
        let testCase = lambda "getOpt" $ lambda "x" $
                         (matchOpt
                           (string "nothing")
                           (lambda "t2" $ string "just")) @@ (var "getOpt" @@ var "x")
        let getOptType = (Types.function (Types.var "t1") (Types.optional $ Types.var "t4"))
        let constStringType = Types.function (Types.var "t1") Types.string
        expectTypeAnnotation pure testCase
          (Types.function getOptType constStringType)
        expectTypeAnnotation Expect.lambdaBody testCase
          constStringType

    H.describe "Check unannotated 'let' terms" $ do
      H.it "test #1" $ do
        let testCase = lambda "i" $
                         (Terms.primitive _strings_cat @@ list [string "foo", var "i", string "bar"])
                         `with` [
                           "foo">: string "FOO",
                           "bar">: string "BAR"]
        expectTypeAnnotation pure testCase
          (Types.function Types.string Types.string)
        expectTypeAnnotation Expect.lambdaBody testCase
          Types.string
      H.it "test #2" $ do
        let testCase = lambda "original" $
                         var "alias" `with` [
                           "alias">: var "original"]
        expectTypeAnnotation pure testCase
          (Types.function (Types.var "t0") (Types.var "t0"))
        expectTypeAnnotation Expect.lambdaBody testCase
          (Types.var "t0")
        expectTypeAnnotation (Expect.lambdaBody >=> Expect.letBinding "alias") testCase
          (Types.var "t0")
      H.it "test #3" $ do
        let testCase = lambda "fun" $ lambda "t" $
                         ((var "funAlias" @@ var "t") `with` [
                           "funAlias">: var "fun"])
        let funType = Types.function (Types.var "t1") (Types.var "t2")
        expectTypeAnnotation pure testCase
          (Types.function funType funType)
        expectTypeAnnotation (Expect.lambdaBody >=> Expect.lambdaBody) testCase
          (Types.var "t2")
        expectTypeAnnotation (Expect.lambdaBody >=> Expect.lambdaBody >=> Expect.letBinding "funAlias") testCase
          funType

--     H.describe "Check 'let' terms with type annotations on bindings" $

  where
    tmp term = shouldSucceedWith flow ()
      where
        flow = do
          iterm <- annotateTermWithTypes term
          fail $ "iterm: " ++ show iterm


checkTypedTerms :: H.SpecWith ()
checkTypedTerms = H.describe "Check that term/type pairs are consistent with type inference" $ do

    H.it "Check arbitrary typed terms" $
      QC.property $ \(TypedTerm typ term) -> expectMonotype term typ

spec :: H.Spec
spec = do
  checkApplicationTerms
  checkFunctionTerms
  checkIndividualTerms
  checkLetTerms
  checkLists
  checkLiterals
  checkWrappedTerms
  checkPrimitives
  checkProducts
  checkSums
  checkTypeAnnotations
  checkSubtermAnnotations
--  checkTypedTerms
