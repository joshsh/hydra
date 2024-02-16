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
import Hydra.Dsl.ShorthandTypes

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad


checkType :: Term -> Type -> H.Expectation
checkType term typ = expectTypeAnnotation pure term typ

-- TODO: move into the Terms DSL when practical
typed :: Type -> Term -> Term
typed typ = setTermType (Just typ)

expectFailure :: Term -> H.Expectation
expectFailure term = do
  shouldFail (inferredTypeOf term)

expectType :: Term -> Type -> H.Expectation
expectType term typ = do
  shouldSucceedWith
    (inferredTypeOf term)
    typ

expectPolytype :: Term -> [String] -> Type -> H.Expectation
expectPolytype term vars typ = do
  shouldSucceedWith
    (inferredTypeOf term)
    (Types.lambdas vars typ)

expectRawType :: Term -> Type -> H.Expectation
expectRawType term typ = do
  shouldSucceedWith
    (inferredType <$> infer term)
    typ

expectTypeAnnotation :: (Term -> Flow Graph Term) -> Term -> Type -> H.Expectation
expectTypeAnnotation path term etyp = shouldSucceedWith atyp etyp
  where
   atyp = do
     iterm <- inferTermType term
     selected <- path iterm
     mtyp <- getType (termAnnotation selected)
     case mtyp of
       Nothing -> fail $ "no type annotation"
       Just t -> pure t

checkEliminations :: H.SpecWith ()
checkEliminations = H.describe "Check a few hand-picked elimination terms" $ do

  H.it "Match statements" $ do
    expectType
      (match simpleNumberName Nothing [
        Field (FieldName "int") $ lambda "x" $ var "x",
        Field (FieldName "float") $ lambda "x" $ int32 42])
      (funT (TypeVariable simpleNumberName) Types.int32)

checkFunctionTerms :: H.SpecWith ()
checkFunctionTerms = H.describe "Check a few hand-picked function terms" $ do

  H.describe "Lambdas" $ do
    H.it "test #1" $
      expectPolytype
        (lambda "x" $ var "x")
        ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))
    H.it "test #2" $
      expectPolytype
        (lambda "x" $ int16 137)
        ["t0"] (Types.function (Types.var "t0") Types.int16)

  H.describe "List eliminations (folds)" $ do
    let fun = Terms.fold $ primitive _math_add
    H.it "test #1" $
      expectType
        fun
        (Types.functionN [Types.int32, Types.list Types.int32, Types.int32])
    H.it "test #2" $
      expectType
        (fun @@ int32 0)
        (Types.function (Types.list Types.int32) Types.int32)
    H.it "test #3" $
      expectType
        (fun @@ int32 0 @@ (list (int32 <$> [1, 2, 3, 4, 5])))
        Types.int32

  H.it "Projections" $ do
    expectType
      (project testTypePersonName (FieldName "firstName"))
      (Types.function (TypeVariable testTypePersonName) Types.string)

  H.it "Union eliminations (case statements)" $ do
    expectType
      (match testTypeFoobarValueName Nothing [
        Field (FieldName "bool") (lambda "x" (boolean True)),
        Field (FieldName "string") (lambda "x" (boolean False)),
        Field (FieldName "unit") (lambda "x" (boolean False))])
      (Types.function (TypeVariable testTypeFoobarValueName) Types.boolean)

checkIndividualTerms :: H.SpecWith ()
checkIndividualTerms = H.describe "Check a few hand-picked terms" $ do

  H.describe "Literal values" $ do
    H.it "test #1" $
      expectType
        (int32 42)
        Types.int32
    H.it "test #2" $
      expectType
        (string "foo")
        Types.string
    H.it "test #3" $
      expectType
        (boolean False)
        Types.boolean
    H.it "test #4" $
      expectType
        (float64 42.0)
        Types.float64

  H.it "Let terms" $ do
    expectPolytype
      (letTerm (Name "x") (float32 42.0) (lambda "y" (lambda "z" (var "x"))))
      ["t0", "t1"] (Types.function (Types.var "t0") (Types.function (Types.var "t1") Types.float32))

  H.describe "Optionals" $ do
    H.it "test #1" $
      expectType
        (optional $ Just $ int32 42)
        (Types.optional Types.int32)
    H.it "test #2" $
      expectPolytype
        (optional Nothing)
        ["t0"] (Types.optional $ Types.var "t0")

  H.describe "Records" $ do
    H.it "test #1" $
      expectType
        (record latLonName [
          Field (FieldName "lat") $ float32 37.7749,
          Field (FieldName "lon") $ float32 $ negate 122.4194])
        (TypeVariable latLonName)
    H.it "test #2" $
      expectType
        (record latLonPolyName [
          Field (FieldName "lat") $ float32 37.7749,
          Field (FieldName "lon") $ float32 $ negate 122.4194])
        (Types.apply (TypeVariable latLonPolyName) Types.float32)
    H.it "test #3" $
      expectType
        (lambda "lon" (record latLonPolyName [
          Field (FieldName "lat") $ float32 37.7749,
          Field (FieldName "lon") $ var "lon"]))
        (Types.function (Types.float32) (Types.apply (TypeVariable latLonPolyName) Types.float32))
    H.it "test #4" $
      expectPolytype
        (lambda "latlon" (record latLonPolyName [
          Field (FieldName "lat") $ var "latlon",
          Field (FieldName "lon") $ var "latlon"]))
        ["t0"] (Types.function (Types.var "t0") (Types.apply (TypeVariable latLonPolyName) (Types.var "t0")))

  H.describe "Record instances of simply recursive record types" $ do
    H.it "test #1" $
      expectType
        (record testTypeIntListName [
          Field (FieldName "head") $ int32 42,
          Field (FieldName "tail") $ optional $ Just $ record testTypeIntListName [
            Field (FieldName "head") $ int32 43,
            Field (FieldName "tail") $ optional Nothing]])
        (TypeVariable testTypeIntListName)
    H.it "test #2" $
      expectType
        ((lambda "x" $ record testTypeIntListName [
          Field (FieldName "head") $ var "x",
          Field (FieldName "tail") $ optional $ Just $ record testTypeIntListName [
            Field (FieldName "head") $ var "x",
            Field (FieldName "tail") $ optional Nothing]]) @@ int32 42)
        (TypeVariable testTypeIntListName)
    H.it "test #3" $
      expectType
        (record testTypeListName [
          Field (FieldName "head") $ int32 42,
          Field (FieldName "tail") $ optional $ Just $ record testTypeListName [
            Field (FieldName "head") $ int32 43,
            Field (FieldName "tail") $ optional Nothing]])
        (Types.apply (TypeVariable testTypeListName) Types.int32)
    H.it "test #4" $
      expectType
        ((lambda "x" $ record testTypeListName [
          Field (FieldName "head") $ var "x",
          Field (FieldName "tail") $ optional $ Just $ record testTypeListName [
            Field (FieldName "head") $ var "x",
            Field (FieldName "tail") $ optional Nothing]]) @@ int32 42)
        (Types.apply (TypeVariable testTypeListName) Types.int32)
    H.it "test #5" $
      expectPolytype
        (lambda "x" $ record testTypeListName [
          Field (FieldName "head") $ var "x",
          Field (FieldName "tail") $ optional $ Just $ record testTypeListName [
            Field (FieldName "head") $ var "x",
            Field (FieldName "tail") $ optional Nothing]])
        ["t0"] (Types.function (Types.var "t0") (Types.apply (TypeVariable testTypeListName) (Types.var "t0")))

  H.describe "Record instances of mutually recursive record types" $ do
    H.it "test #1" $
      expectType
        ((lambda "x" $ record testTypeBuddyListAName [
          Field (FieldName "head") $ var "x",
          Field (FieldName "tail") $ optional $ Just $ record testTypeBuddyListBName [
            Field (FieldName "head") $ var "x",
            Field (FieldName "tail") $ optional Nothing]]) @@ int32 42)
        (Types.apply (TypeVariable testTypeBuddyListAName) Types.int32)
    H.it "test #2" $
      expectPolytype
        (lambda "x" $ record testTypeBuddyListAName [
          Field (FieldName "head") $ var "x",
          Field (FieldName "tail") $ optional $ Just $ record testTypeBuddyListBName [
            Field (FieldName "head") $ var "x",
            Field (FieldName "tail") $ optional Nothing]])
        ["t0"] (Types.function (Types.var "t0") (Types.apply (TypeVariable testTypeBuddyListAName) (Types.var "t0")))

  H.it "Unions" $ do
    expectType
      (inject testTypeTimestampName $ Field (FieldName "unixTimeMillis") $ uint64 1638200308368)
      (TypeVariable testTypeTimestampName)

  H.describe "Sets" $ do
    H.it "test #1" $
      expectType
        (set $ S.fromList [boolean True])
        (Types.set Types.boolean)
    H.it "test #2" $
      expectPolytype
        (set $ S.fromList [set S.empty])
        ["t0"] (Types.set $ Types.set $ Types.var "t0")

  H.describe "Maps" $ do
    H.it "test #1" $
      expectType
        (mapTerm $ M.fromList [(string "firstName", string "Arthur"), (string "lastName", string "Dent")])
        (Types.map Types.string Types.string)
    H.it "test #2" $
      expectPolytype
        (mapTerm M.empty)
        ["t0", "t1"] (Types.map (Types.var "t0") (Types.var "t1"))
    H.it "test #3" $
      expectPolytype
        (lambda "x" (lambda "y" (mapTerm $ M.fromList
          [(var "x", float64 0.1), (var "y", float64 0.2)])))
        ["t0"] (Types.function (Types.var "t0") (Types.function (Types.var "t0") (Types.map (Types.var "t0") Types.float64)))

--    H.it "Check nominal (newtype) terms" $ do
--      expectType
--        testDataArthur
--        (Types.wrap "Person")
    --   expectType
    --     (lambda "x" (record [
    --       Field "firstName" $ var "x",
    --       Field "lastName" $ var "x",
    --       Field "age" $ int32 42]))
    --     (Types.function Types.string testTypePerson)

checkLetTerms :: H.SpecWith ()
checkLetTerms = H.describe "Check a few hand-picked let terms" $ do

  H.it "Empty let" $ do
    expectType
      ((int32 42) `with` [])
      Types.int32

  H.it "Trivial let" $ do
    expectType
      (var "foo" `with` [
        "foo">: int32 42])
      Types.int32

  H.it "Multiple references to a let-bound term" $
    expectType
      (list [var "foo", var "bar", var "foo"] `with` [
        "foo">: int32 42,
        "bar">: int32 137])
      (Types.list Types.int32)

  H.describe "Let-polymorphism" $ do
    H.it "test #1" $
      expectPolytype
        ((lambda "x" $ var "id" @@ (var "id" @@ var "x")) `with` [
          "id">: lambda "x" $ var "x"])
        ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))
    H.it "test #2" $
      expectType
        ((var "id" @@ (list [var "id" @@ int32 42])) `with` [
          "id">: lambda "x" $ var "x"])
        (Types.list Types.int32)
    H.it "test #3" $
      expectPolytype
        ((lambda "x" (var "id" @@ (list [var "id" @@ var "x"])))
          `with` [
            "id">: lambda "x" $ var "x"])
        ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #4" $
      expectType
        ((pair (var "id" @@ int32 42) (var "id" @@ string "foo"))
          `with` [
            "id">: lambda "x" $ var "x"])
        (Types.pair Types.int32 Types.string)
    H.it "test #5" $
      expectType
        ((pair (var "list" @@ int32 42) (var "list" @@ string "foo"))
          `with` [
            "list">: lambda "x" $ list [var "x"]])
        (Types.pair (Types.list Types.int32) (Types.list Types.string))

  H.describe "Recursive and mutually recursive let (@wisnesky's test cases)" $ do
--    H.it "test #1" $
--      expectPolytype
--        ((var "f") `with` [
--          "f">: lambda "x" $ lambda "y" (var "f" @@ int32 0 @@ var "x")])
--        ["t0"] (Types.function Types.int32 (Types.function Types.int32 (Types.var "t0")))
    H.it "test #2" $
      expectPolytype
        ((pair (var "f") (var "g")) `with` [
          "f">: var "g",
          "g">: var "f"])
        -- Note: Haskell fails to unify the left and right types, giving forall ab. (a, b)
        ["t0"] (Types.pair (Types.var "t0") (Types.var "t0"))
--    H.it "test #3" $
--      expectPolytype
--        ((pair (var "f") (var "g")) `with` [
--          "f">: lambda "x" $ lambda "y" (var "g" @@ int32 0 @@ var "x"),
--          "g">: lambda "u" $ lambda "v" (var "f" @@ var "v" @@ int32 0)])
--        ["t0", "t1"] (Types.pair
--          (Types.function (Types.var "v0") (Types.function Types.int32 (Types.var "t1")))
--          (Types.function Types.int32 (Types.function (Types.var "v0") (Types.var "t1"))))

checkLists :: H.SpecWith ()
checkLists = H.describe "Check a few hand-picked list terms" $ do

  H.it "List of strings" $
    expectType
      (list [string "foo", string "bar"])
      (Types.list Types.string)
  H.it "List of lists of strings" $
    expectType
      (list [list [string "foo"], list []])
      (Types.list $ Types.list Types.string)
  H.it "Empty list" $
    expectPolytype
      (list [])
      ["t0"] (Types.list $ Types.var "t0")
  H.it "List containing an empty list" $
    expectPolytype
      (list [list []])
      ["t0"] (Types.list $ Types.list $ Types.var "t0")
  H.it "Lambda producing a polymorphic list" $
    expectPolytype
      (lambda "x" (list [var "x"]))
      ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
  H.it "Lambda producing a list of integers" $
    expectType
      (lambda "x" (list [var "x", int32 42]))
      (Types.function Types.int32 $ Types.list Types.int32)
  H.it "List with repeated variables" $
    expectType
      (lambda "x" (list [var "x", string "foo", var "x"]))
      (Types.function Types.string (Types.list Types.string))

checkLiterals :: H.SpecWith ()
checkLiterals = H.describe "Check arbitrary literals" $ do

  H.it "Verify that type inference preserves the literal to literal type mapping" $
    QC.property $ \l -> expectType
      (TermLiteral l)
      (Types.literal $ literalType l)

checkPathologicalTerms :: H.SpecWith ()
checkPathologicalTerms = H.describe "Check pathological terms" $ do

  H.describe "Infinite lists" $ do
    H.it "test #1" $
      expectType
        ((var "self") `with` [
          "self">: primitive _lists_cons @@ (int32 42) @@ (var "self")])
        (Types.list Types.int32)
    H.it "test #2" $
      expectPolytype
        (lambda "x" ((var "self") `with` [
          "self">: primitive _lists_cons @@ (var "x") @@ (var "self")]))
        ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #3" $
      expectPolytype
        ((lambda "x" $ var "self" @@ var "x") `with` [
          "self">: lambda "e" $ primitive _lists_cons @@ (var "e") @@ (var "self" @@ var "e")])
        ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #4" $
      expectType
        ((var "build" @@ int32 0) `with` [
          "build">: lambda "x" $ primitive _lists_cons @@ var "x" @@ (var "build" @@
            (primitive _math_add @@ var "x" @@ int32 1))])
        (Types.list Types.int32)

  -- TODO: this term *should* fail inference, but doesn't
--    H.it "Check self-application" $ do
--      expectFailure
--        (lambda "x" $ var "x" @@ var "x")

checkPolymorphism :: H.SpecWith ()
checkPolymorphism = H.describe "Check polymorphism" $ do

  H.describe "Simple lists and optionals" $ do
    H.it "test #1" $
      expectPolytype
        (list [])
        ["t0"] (Types.list (Types.var "t0"))
    H.it "test #2" $
      expectPolytype
        (optional Nothing)
        ["t0"] (Types.optional (Types.var "t0"))
    H.it "test #3" $
      expectType
        (optional $ Just $ int32 42)
        (Types.optional Types.int32)

  H.describe "Lambdas, lists, and products" $ do
    H.it "test #1" $
      expectPolytype
        (lambda "x" $ var "x")
        ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))
    H.it "test #2" $
      expectPolytype
        (lambda "x" $ pair (var "x") (var "x"))
        ["t0"] (Types.function (Types.var "t0") (Types.pair (Types.var "t0") (Types.var "t0")))
    H.it "test #3" $
      expectPolytype
        (lambda "x" $ list [var "x"])
        ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #4" $
      expectPolytype
        (list [lambda "x" $ var "x", lambda "y" $ var "y"])
        ["t0"] (Types.list $ Types.function (Types.var "t0") (Types.var "t0"))
    H.it "test #5" $
      expectPolytype
        (list [lambda "x" $ lambda "y" $ pair (var "y") (var "x")])
        ["t0", "t1"] (Types.list $ Types.function (Types.var "t0") (Types.function (Types.var "t1") (Types.pair (Types.var "t1") (Types.var "t0"))))

  H.describe "Lambdas and application" $ do
    H.it "test #1" $
      expectType
        (lambda "x" (var "x") @@ string "foo")
        Types.string

  H.describe "Primitives and application" $ do
    H.it "test #1" $
      expectType
        (primitive _lists_concat @@ list [list [int32 42], list []])
        (Types.list Types.int32)

  H.describe "Lambdas and primitives" $ do
    H.it "test #1" $
      expectType
        (primitive _math_add)
        (Types.functionN [Types.int32, Types.int32, Types.int32])
    H.it "test #2" $
      expectType
        (lambda "x" (primitive _math_add @@ var "x"))
        (Types.functionN [Types.int32, Types.int32, Types.int32])
    H.it "test #3" $
      expectType
        (lambda "x" (primitive _math_add @@ var "x" @@ var "x"))
        (Types.function Types.int32 Types.int32)

  H.describe "Mixed expressions with lambdas, constants, and primitive functions" $ do
    H.it "test #1" $
      expectType
        (lambda "x" $
            (primitive _math_sub @@ (primitive _math_add @@ var "x" @@ var "x") @@ int32 1))
        (Types.function Types.int32 Types.int32)

checkPrimitives :: H.SpecWith ()
checkPrimitives = H.describe "Check a few hand-picked terms with primitive functions" $ do

  H.describe "Monomorphic primitive functions" $ do
    H.it "test #1" $
      expectType
        (primitive $ Name "hydra/lib/strings.length")
        (Types.function Types.string Types.int32)
    H.it "test #2" $
      expectType
        (primitive _math_sub)
        (Types.function Types.int32 (Types.function Types.int32 Types.int32))

  H.describe "Polymorphic primitive functions" $ do
    H.it "test #1" $
      expectPolytype
        (lambda "el" (primitive _lists_length @@ (list [var "el"])))
        ["t0"] (Types.function (Types.var "t0") Types.int32)
    H.it "test #2" $
      expectType
        (lambda "el" (primitive _lists_length @@ (list [int32 42, var "el"])))
        (Types.function Types.int32 Types.int32)
    H.it "test #3" $
      expectPolytype
        (primitive _lists_concat)
        ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #4" $
      expectPolytype
        (lambda "lists" (primitive _lists_concat @@ var "lists"))
        ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "test #5" $
      expectPolytype
        (lambda "lists" (primitive _lists_length @@ (primitive _lists_concat @@ var "lists")))
        ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") Types.int32)
    H.it "test #6" $
      expectPolytype
        (lambda "list" (primitive _lists_length @@ (primitive _lists_concat @@ list[var "list", list []])))
        ["t0"] (Types.function (Types.list $ Types.var "t0") Types.int32)
    H.it "test #7" $
      expectPolytype
        (lambda "list" (primitive _math_add
          @@ int32 1
          @@ (primitive _lists_length @@ (primitive _lists_concat @@ list[var "list", list []]))))
        ["t0"] (Types.function (Types.list $ Types.var "t0") Types.int32)
    H.it "test #8" $
      expectPolytype
        (lambda "lists" (primitive _lists_length @@ (primitive _lists_concat @@ var "lists")))
        ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") Types.int32)

checkProducts :: H.SpecWith ()
checkProducts = H.describe "Check a few hand-picked product terms" $ do

  H.it "Empty product" $ do
    expectType
      (Terms.product [])
      (Types.product [])

  H.describe "Non-empty, monotyped products" $ do
    H.it "test #1" $
      expectType
        (Terms.product [string "foo", int32 42])
        (Types.product [Types.string, Types.int32])
    H.it "test #2" $
      expectType
        (Terms.product [string "foo", list [float32 42.0, float32 137.0]])
        (Types.product [Types.string, Types.list Types.float32])
    H.it "test #3" $
      expectType
        (Terms.product [string "foo", int32 42, list [float32 42.0, float32 137.0]])
        (Types.product [Types.string, Types.int32, Types.list Types.float32])

  H.describe "Polytyped products" $ do
    H.it "test #1" $
      expectPolytype
        (Terms.product [list [], string "foo"])
        ["t0"] (Types.product [Types.list $ Types.var "t0", Types.string])
    H.it "test #2" $
      expectPolytype
        (Terms.product [int32 42, "foo", list []])
        ["t0"] (Types.product [Types.int32, Types.string, Types.list $ Types.var "t0"])

  H.describe "Pairs" $ do
    H.it "test #1" $
      expectType
        (pair (int32 42) "foo")
        (Types.pair Types.int32 Types.string)
    H.it "test #2" $
      expectPolytype
        (pair (list []) "foo")
        ["t0"] (Types.pair (Types.list $ Types.var "t0") Types.string)
    H.it "test #3" $
      expectPolytype
        (pair (list []) (list []))
        ["t0", "t1"] (Types.pair (Types.list $ Types.var "t0") (Types.list $ Types.var "t1"))

-- Check inference without unification or top-level normalization
checkRawInference :: H.SpecWith ()
checkRawInference = H.describe "Check raw inference" $ do
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

checkSums :: H.SpecWith ()
checkSums = H.describe "Check a few hand-picked sum terms" $ do

  H.describe "Singleton sum terms" $ do
    H.it "test #1" $
      expectType
        (Terms.sum 0 1 $ string "foo")
        (Types.sum [Types.string])
    H.it "test #2" $
      expectPolytype
        (Terms.sum 0 1 $ list [])
        ["t0"] (Types.sum [Types.list $ Types.var "t0"])

  H.describe "Non-singleton sum terms" $ do
    H.it "test #1" $
      expectPolytype
        (Terms.sum 0 2 $ string "foo")
        ["t0"] (Types.sum [Types.string, Types.var "t0"])
    H.it "test #2" $
      expectPolytype
        (Terms.sum 1 2 $ string "foo")
        ["t0"] (Types.sum [Types.var "t0", Types.string])

checkTypeAnnotations :: H.SpecWith ()
checkTypeAnnotations = H.describe "Check that type annotations are added to terms and subterms" $ do

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
      let (TermAnnotated (Annotated (TermList [term2]) _)) = term1
      checkType term2 (Types.literal $ literalType l)

checkSubtermAnnotations :: H.SpecWith ()
checkSubtermAnnotations = H.describe "Check additional subterm annotations" $ do

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

--checkTypedTerms :: H.SpecWith ()
--checkTypedTerms = H.describe "Check that term/type pairs are consistent with type inference" $ do
--
--    H.it "Arbitrary typed terms" $
--      QC.property $ \(TypedTerm typ term) -> expectType term typ

checkUserProvidedTypes :: H.SpecWith ()
checkUserProvidedTypes = H.describe "Check that user-provided type annotations are respected" $ do

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
          (TermLet $ Let (M.fromList [(Name "x", pretypedEmptyList)]) $ var "x")
          ["p"] (Types.list $ Types.var "p")
      H.it "test #2" $
        expectPolytype
          (TermLet $ Let (M.fromList [(Name "y", pretypedEmptyMap)]) $ var "y")
          ["k", "v"] (Types.map (Types.var "k") (Types.var "v"))
      H.it "test #3" $
        expectPolytype
          (TermLet $ Let (M.fromList [
            (Name "x", pretypedEmptyList),
            (Name "y", pretypedEmptyMap)
            ]) $ Terms.pair (var "x") (var "y"))
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

checkWrappedTerms :: H.SpecWith ()
checkWrappedTerms = H.describe "Check nominal introductions and eliminations" $ do

  H.describe "Nominal introductions" $ do
    H.it "test #1" $
      expectType
        (wrap stringAliasTypeName $ string "foo")
        (TypeVariable stringAliasTypeName)
    H.it "test #2" $
      expectType
        (lambda "v" $ wrap stringAliasTypeName $ var "v")
        (Types.function Types.string (TypeVariable stringAliasTypeName))

  H.it "Nominal eliminations" $ do
--    expectType
--      (unwrap stringAliasTypeName)
--      (Types.function stringAliasType (Ann.doc "An alias for the string type" Types.string))
    expectType
      (unwrap stringAliasTypeName @@ (wrap stringAliasTypeName $ string "foo"))
      Types.string

executeFlow = fromFlow (TermLiteral $ LiteralString "no term") testGraph

spec :: H.Spec
spec = do
  checkEliminations
  checkFunctionTerms
  checkIndividualTerms
  checkLetTerms
  checkLists
  checkLiterals
  checkPathologicalTerms
  checkPolymorphism
  checkPrimitives
  checkProducts
  checkSubtermAnnotations
  checkSums
  checkTypeAnnotations
  checkWrappedTerms

  checkRawInference

--  checkTypedTerms -- (excluded for now)
--  checkUserProvidedTypes -- disabled for now; user-provided type variables are replaced with fresh variables
