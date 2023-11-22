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

expectMonotype :: Term -> Type -> H.Expectation
expectMonotype term = expectPolytype term []

expectPolytype :: Term -> [String] -> Type -> H.Expectation
expectPolytype term vars typ = do
    shouldSucceedWith
      (inferredTypeOf term)
      (Types.lambdas vars typ)

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

  H.it "Check match statements" $ do
    expectMonotype
      (match simpleNumberName Nothing [
        Field (FieldName "int") $ lambda "x" $ var "x",
        Field (FieldName "float") $ lambda "x" $ int32 42])
      (funT (TypeVariable simpleNumberName) Types.int32)

checkFunctionTerms :: H.SpecWith ()
checkFunctionTerms = H.describe "Check a few hand-picked function terms" $ do

    H.describe "Check lambdas" $ do
      H.it "test #1" $ do
        expectPolytype
          (lambda "x" $ var "x")
          ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))
      H.it "test #2" $ do
        expectPolytype
          (lambda "x" $ int16 137)
          ["t0"] (Types.function (Types.var "t0") Types.int16)

    H.it "Check list eliminations" $ do
      let fun = Terms.fold $ primitive _math_add
      expectMonotype
        fun
        (Types.functionN [Types.int32, Types.list Types.int32, Types.int32])
      expectMonotype
        (fun @@ int32 0)
        (Types.function (Types.list Types.int32) Types.int32)
      expectMonotype
        (fun @@ int32 0 @@ (list (int32 <$> [1, 2, 3, 4, 5])))
        Types.int32

    H.it "Check projections" $ do
      expectMonotype
        (project testTypePersonName (FieldName "firstName"))
        (Types.function (TypeVariable testTypePersonName) Types.string)

    H.it "Check case statements" $ do
      expectMonotype
        (match testTypeFoobarValueName Nothing [
          Field (FieldName "bool") (lambda "x" (boolean True)),
          Field (FieldName "string") (lambda "x" (boolean False)),
          Field (FieldName "unit") (lambda "x" (boolean False))])
        (Types.function (TypeVariable testTypeFoobarValueName) Types.boolean)

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

    H.describe "Check records" $ do
      H.it "test #1" $ do
        expectMonotype
          (record latLonName [
            Field (FieldName "lat") $ float32 37.7749,
            Field (FieldName "lon") $ float32 $ negate 122.4194])
          (TypeVariable latLonName)
      H.it "test #2" $ do
        expectMonotype
          (record latLonPolyName [
            Field (FieldName "lat") $ float32 37.7749,
            Field (FieldName "lon") $ float32 $ negate 122.4194])
          (Types.apply (TypeVariable latLonPolyName) Types.float32)
      H.it "test #3" $ do
        expectMonotype
          (lambda "lon" (record latLonPolyName [
            Field (FieldName "lat") $ float32 37.7749,
            Field (FieldName "lon") $ var "lon"]))
          (Types.function (Types.float32) (Types.apply (TypeVariable latLonPolyName) Types.float32))
      H.it "test #4" $ do
        expectPolytype
          (lambda "latlon" (record latLonPolyName [
            Field (FieldName "lat") $ var "latlon",
            Field (FieldName "lon") $ var "latlon"]))
          ["t0"] (Types.function (Types.var "t0") (Types.apply (TypeVariable latLonPolyName) (Types.var "t0")))

    H.it "Check unions" $ do
      expectMonotype
        (inject testTypeTimestampName $ Field (FieldName "unixTimeMillis") $ uint64 1638200308368)
        (TypeVariable testTypeTimestampName)

    H.describe "Check sets" $ do
      H.it "test #1" $ do
        expectMonotype
          (set $ S.fromList [boolean True])
          (Types.set Types.boolean)
      H.it "test #2" $ do
        expectPolytype
          (set $ S.fromList [set S.empty])
          ["t0"] (Types.set $ Types.set $ Types.var "t0")

    H.describe "Check maps" $ do
      H.it "test #1" $ do
        expectMonotype
          (mapTerm $ M.fromList [(string "firstName", string "Arthur"), (string "lastName", string "Dent")])
          (Types.map Types.string Types.string)
      H.it "test #2" $ do
        expectPolytype
          (mapTerm M.empty)
          ["t0", "t1"] (Types.map (Types.var "t0") (Types.var "t1"))
      H.it "test #3" $ do
        expectPolytype
          (lambda "x" (lambda "y" (mapTerm $ M.fromList
            [(var "x", float64 0.1), (var "y", float64 0.2)])))
          ["t0"] (Types.function (Types.var "t0") (Types.function (Types.var "t0") (Types.map (Types.var "t0") Types.float64)))

    -- -- TODO: add a case for a recursive nominal type -- e.g. MyList := () + (int, Mylist)
--    H.it "Check nominal (newtype) terms" $ do
--      expectMonotype
--        testDataArthur
--        (Types.wrap "Person")
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
    H.it "Check lambda producing a polymorphic list" $ do
      expectPolytype
        (lambda "x" (list [var "x"]))
        ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
    H.it "Check lambda producing a list of integers" $ do
      expectMonotype
        (lambda "x" (list [var "x", int32 42]))
        (Types.function Types.int32 $ Types.list Types.int32)
    H.it "Check list with repeated variables" $ do
      expectMonotype
        (lambda "x" (list [var "x", string "foo", var "x"]))
        (Types.function Types.string (Types.list Types.string))

checkLiterals :: H.SpecWith ()
checkLiterals = H.describe "Check arbitrary literals" $ do

    H.it "Verify that type inference preserves the literal to literal type mapping" $
      QC.property $ \l -> expectMonotype
        (TermLiteral l)
        (Types.literal $ literalType l)

checkPathologicalTypes :: H.SpecWith ()
checkPathologicalTypes = H.describe "Check pathological types" $ do
--    -- TODO
--    H.it "Check self-application" $ do
--      expectFailure
--        (lambda "x" $ var "x" @@ var "x")

    return ()

checkPolymorphism :: H.SpecWith ()
checkPolymorphism = H.describe "Check polymorphism" $ do

    H.describe "Simple lists and optionals" $ do
      H.it "test #1" $ do
        expectPolytype
          (list [])
          ["t0"] (Types.list (Types.var "t0"))
      H.it "test #2" $ do
        expectPolytype
          (optional Nothing)
          ["t0"] (Types.optional (Types.var "t0"))
      H.it "test #3" $ do
        expectMonotype
          (optional $ Just $ int32 42)
          (Types.optional Types.int32)

    H.describe "Products" $ do
      H.it "test #1" $ do
        expectMonotype
          (pair (int32 42) "foo")
          (Types.pair Types.int32 Types.string)
      H.it "test #2" $ do
        expectPolytype
          (pair (list []) "foo")
          ["t0"] (Types.pair (Types.list $ Types.var "t0") Types.string)
      H.it "test #3" $ do
        expectPolytype
          (pair (list []) (list []))
          ["t0", "t1"] (Types.pair (Types.list $ Types.var "t0") (Types.list $ Types.var "t1"))

    H.describe "Lambdas, lists, and products" $ do
      H.it "test #1" $ do
        expectPolytype
          (lambda "x" $ var "x")
          ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))
      H.it "test #2" $ do
        expectPolytype
          (lambda "x" $ pair (var "x") (var "x"))
          ["t0"] (Types.function (Types.var "t0") (Types.pair (Types.var "t0") (Types.var "t0")))
      H.it "test #3" $ do
        expectPolytype
          (lambda "x" $ list [var "x"])
          ["t0"] (Types.function (Types.var "t0") (Types.list $ Types.var "t0"))
      H.it "test #4" $ do
        expectPolytype
          (list [lambda "x" $ var "x", lambda "y" $ var "y"])
          ["t0"] (Types.list $ Types.function (Types.var "t0") (Types.var "t0"))
      H.it "test #5" $ do
        expectPolytype
          (list [lambda "x" $ lambda "y" $ pair (var "y") (var "x")])
          ["t0", "t1"] (Types.list $ Types.function (Types.var "t0") (Types.function (Types.var "t1") (Types.pair (Types.var "t1") (Types.var "t0"))))

    H.describe "Lambdas and application" $ do
      H.it "test #1" $ do
        expectMonotype
          (lambda "x" (var "x") @@ string "foo")
          Types.string

    H.describe "Primitives and application" $ do
      H.it "test #1" $ do
        expectMonotype
          (primitive _lists_concat @@ list [list [int32 42], list []])
          (Types.list Types.int32)

    H.describe "Lambdas and primitives" $ do
      H.it "test #1" $ do
        expectMonotype
          (primitive _math_add)
          (Types.functionN [Types.int32, Types.int32, Types.int32])
      H.it "test #2" $ do
        expectMonotype
          (lambda "x" (primitive _math_add @@ var "x"))
          (Types.functionN [Types.int32, Types.int32, Types.int32])
      H.it "test #3" $ do
        expectMonotype
          (lambda "x" (primitive _math_add @@ var "x" @@ var "x"))
          (Types.function Types.int32 Types.int32)

    H.describe "Mixed expressions with lambdas, constants, and primitive functions" $ do
      H.it "test #1" $ do
        expectMonotype
          (lambda "x" $
              (primitive _math_sub @@ (primitive _math_add @@ var "x" @@ var "x") @@ int32 1))
          (Types.function Types.int32 Types.int32)

checkPrimitives :: H.SpecWith ()
checkPrimitives = H.describe "Check a few hand-picked terms with primitive functions" $ do

    H.describe "Check monomorphic primitive functions" $ do
      H.it "test #1" $ do
        expectMonotype
          (primitive $ Name "hydra/lib/strings.length")
          (Types.function Types.string Types.int32)
      H.it "test #2" $ do
        expectMonotype
          (primitive _math_sub)
          (Types.function Types.int32 (Types.function Types.int32 Types.int32))

    H.describe "Check polymorphic primitive functions" $ do
      H.it "test #1" $ do
        expectPolytype
          (lambda "el" (primitive _lists_length @@ (list [var "el"])))
          ["t0"] (Types.function (Types.var "t0") Types.int32)
      H.it "test #2" $ do
        expectMonotype
          (lambda "el" (primitive _lists_length @@ (list [int32 42, var "el"])))
          (Types.function Types.int32 Types.int32)
      H.it "test #3" $ do
        expectPolytype
          (primitive _lists_concat)
          ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") (Types.list $ Types.var "t0"))
      H.it "test #4" $ do
        expectPolytype
          (lambda "lists" (primitive _lists_concat @@ var "lists"))
          ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") (Types.list $ Types.var "t0"))
      H.it "test #5" $ do
        expectPolytype
          (lambda "lists" (primitive _lists_length @@ (primitive _lists_concat @@ var "lists")))
          ["t0"] (Types.function (Types.list $ Types.list $ Types.var "t0") Types.int32)
      H.it "test #6" $ do
        expectPolytype
          (lambda "list" (primitive _lists_length @@ (primitive _lists_concat @@ list[var "list", list []])))
          ["t0"] (Types.function (Types.list $ Types.var "t0") Types.int32)
      H.it "test #7" $ do
        expectPolytype
          (lambda "list" (primitive _math_add
            @@ int32 1
            @@ (primitive _lists_length @@ (primitive _lists_concat @@ list[var "list", list []]))))
          ["t0"] (Types.function (Types.list $ Types.var "t0") Types.int32)

      H.it "test #8" $ do
        expectPolytype
          (lambda "lists" (primitive _lists_length @@ (primitive _lists_concat @@ var "lists")))
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
        let term1 = executeFlow (inferTermType term)
        checkType term1 (Types.literal $ literalType l)

    H.it "Check lists of literals" $
      QC.property $ \l -> do
        let term = TermList [TermLiteral l]
        let term1 = executeFlow (inferTermType term)
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

    H.describe "Check injections" $ do
      H.it "test #1" $ do
        expectTypeAnnotation pure
          (inject testTypeTimestampName $ Field (FieldName "date") $ string "2023-05-11")
          (TypeVariable testTypeTimestampName)
      H.it "test #2" $ do
        expectTypeAnnotation pure
          (lambda "ignored" $ (inject testTypeTimestampName $ Field (FieldName "date") $ string "2023-05-11"))
          (Types.lambda "t0" $ Types.function (Types.var "t0") (TypeVariable testTypeTimestampName))

    H.it "Check projections" $ do
      expectTypeAnnotation pure
        (project testTypePersonName $ FieldName "firstName")
        (Types.function (TypeVariable testTypePersonName) Types.string)

    H.describe "Check case statements" $ do
      H.it "test #1" $ do
        expectTypeAnnotation pure
          (match testTypeNumberName (Just $ string "it's something else") [
            Field (FieldName "int") $ constant $ string "it's an integer"])
          (Types.function (TypeVariable testTypeNumberName) Types.string)
      H.it "test #2" $ do
        let  testCase = match testTypeNumberName Nothing [
                          Field (FieldName "int") $ constant $ string "it's an integer",
                          Field (FieldName "float") $ constant $ string "it's a float"]
        expectTypeAnnotation pure testCase
          (Types.function (TypeVariable testTypeNumberName) Types.string)
        expectTypeAnnotation (Expect.casesCase testTypeNumberName "int" >=> (pure . fieldTerm)) testCase
          (Types.function Types.int32 Types.string)

    H.describe "Check optional eliminations" $ do
      H.describe "test #1" $ do
        let testCase = matchOpt
                         (string "nothing")
                         (lambda "ignored" $ string "just")
        H.it "condition #1" $ do
          expectTypeAnnotation pure testCase
            (Types.lambda "t0" $ Types.function (Types.optional $ Types.var "t0") Types.string)
        H.it "condition #2" $ do
          expectTypeAnnotation Expect.optCasesNothing testCase
            Types.string
        H.it "condition #3" $ do
          expectTypeAnnotation Expect.optCasesJust testCase
            (Types.lambda "t0" $ Types.function (Types.var "t0") Types.string)
      H.describe "test #2" $ do
        let testCase = lambda "getOpt" $ lambda "x" $
                         (matchOpt
                           (string "nothing")
                           (lambda "_" $ string "just")) @@ (var "getOpt" @@ var "x")
        let getOptType = (Types.function (Types.var "t0") (Types.optional $ Types.var "t1"))
        let constStringType = Types.function (Types.var "t0") Types.string
        H.it "condition #1" $ do
          expectTypeAnnotation pure testCase
            (Types.lambdas ["t0", "t1"] $ Types.function getOptType constStringType)
        H.it "condition #2" $ do
          expectTypeAnnotation Expect.lambdaBody testCase
            (Types.lambda "t0" $ constStringType)

    H.describe "Check unannotated 'let' terms" $ do
      H.describe "test #1" $ do
        let testCase = lambda "i" $
                         (Terms.primitive _strings_cat @@ list [string "foo", var "i", string "bar"])
                         `with` [
                           "foo">: string "FOO",
                           "bar">: string "BAR"]
        H.it "condition #1" $ do
          expectTypeAnnotation pure testCase
            (Types.function Types.string Types.string)
        H.it "condition #2" $ do
          expectTypeAnnotation Expect.lambdaBody testCase
            Types.string
      H.describe "test #2" $ do
        let testCase = lambda "original" $
                         var "alias" `with` [
                           "alias">: var "original"]
        H.it "condition #1" $ do
          expectTypeAnnotation pure testCase
            (Types.lambda "t0" $ Types.function (Types.var "t0") (Types.var "t0"))
        H.it "condition #2" $ do
          expectTypeAnnotation Expect.lambdaBody testCase
            (Types.lambda "t0" $ Types.var "t0")
        H.it "condition #3" $ do
          expectTypeAnnotation (Expect.lambdaBody >=> Expect.letBinding "alias") testCase
            (Types.lambda "t0" $ Types.var "t0")
      H.describe "test #3" $ do
        let testCase = lambda "fun" $ lambda "t" $
                         ((var "funAlias" @@ var "t") `with` [
                           "funAlias">: var "fun"])
        let funType = Types.function (Types.var "t0") (Types.var "t1")
        H.it "condition #1" $ do
          expectTypeAnnotation pure testCase
            (Types.lambdas ["t0", "t1"] $ Types.function funType funType)
        H.it "condition #2" $ do
          expectTypeAnnotation (Expect.lambdaBody >=> Expect.lambdaBody) testCase
            (Types.lambda "t1" $ Types.var "t1")
        H.it "condition #3" $ do
          expectTypeAnnotation (Expect.lambdaBody >=> Expect.lambdaBody >=> Expect.letBinding "funAlias") testCase
            (Types.lambda "t0" $ Types.lambda "t1" funType)
  where
    tmp term = shouldSucceedWith flow ()
      where
        flow = do
          iterm <- inferTermType term
          fail $ "iterm: " ++ show iterm

--checkTypedTerms :: H.SpecWith ()
--checkTypedTerms = H.describe "Check that term/type pairs are consistent with type inference" $ do
--
--    H.it "Check arbitrary typed terms" $
--      QC.property $ \(TypedTerm typ term) -> expectMonotype term typ

checkUserProvidedTypes :: H.SpecWith ()
checkUserProvidedTypes = H.describe "Check that user-provided type annotations are respected" $ do

    H.it "Check top-level type annotations" $ do
      expectPolytype
        pretypedEmptyList
        ["p"] (Types.list $ Types.var "p")
      expectPolytype
        pretypedEmptyMap
        ["k", "v"] (Types.map (Types.var "k") (Types.var "v"))

    H.it "Check type annotations on let-bound terms" $ do
      expectPolytype
        (TermLet $ Let (M.fromList [(Name "x", pretypedEmptyList)]) $ var "x")
        ["p"] (Types.list $ Types.var "p")
      expectPolytype
        (TermLet $ Let (M.fromList [(Name "y", pretypedEmptyMap)]) $ var "y")
        ["k", "v"] (Types.map (Types.var "k") (Types.var "v"))
      expectPolytype
        (TermLet $ Let (M.fromList [
          (Name "x", pretypedEmptyList),
          (Name "y", pretypedEmptyMap)
          ]) $ Terms.pair (var "x") (var "y"))
        ["p", "k", "v"] (Types.pair (Types.list $ Types.var "p") (Types.map (Types.var "k") (Types.var "v")))

    H.describe "Check that type variables in subterm annotations are *not* preserved" $ do
      H.it "test #1" $ do
        expectPolytype
          (typed (Types.function (Types.var "a") (Types.var "a")) $ lambda "x" $ var "x")
          ["a"] (Types.function (Types.var "a") (Types.var "a"))
      H.it "test #2" $ do
        expectPolytype
          (typed (Types.lambda "a" $ Types.function (Types.var "a") (Types.var "a")) $ lambda "x" $ var "x")
          ["a"] (Types.function (Types.var "a") (Types.var "a"))
      H.it "test #3" $ do
        expectPolytype
          (lambda "x" $ typed (Types.var "a") $ var "x")
          ["t0"] (Types.function (Types.var "t0") (Types.var "t0"))

  where
    pretypedEmptyList = typed (Types.list $ Types.var "p") $ list []
    pretypedEmptyMap = typed (Types.map (Types.var "k") (Types.var "v")) $ TermMap M.empty

checkWrappedTerms :: H.SpecWith ()
checkWrappedTerms = H.describe "Check nominal introductions and eliminations" $ do

    H.describe "Check nominal introductions" $ do
      H.it "test #1" $
        expectMonotype
          (wrap stringAliasTypeName $ string "foo")
          (TypeVariable stringAliasTypeName)
      H.it "test #2" $
        expectMonotype
          (lambda "v" $ wrap stringAliasTypeName $ var "v")
          (Types.function Types.string (TypeVariable stringAliasTypeName))

    H.it "Check nominal eliminations" $ do
--       expectMonotype
--         (unwrap stringAliasTypeName)
--         (Types.function stringAliasType (Ann.doc "An alias for the string type" Types.string))
      expectMonotype
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
  checkPathologicalTypes
  checkPolymorphism
  checkPrimitives
  checkProducts
  checkSubtermAnnotations
  checkSums
  checkTypeAnnotations
--  checkTypedTerms -- (excluded for now)
  checkUserProvidedTypes
  checkWrappedTerms
