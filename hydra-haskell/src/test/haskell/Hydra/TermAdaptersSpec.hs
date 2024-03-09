module Hydra.TermAdaptersSpec where

import Hydra.Kernel
import Hydra.TermAdapters
import Hydra.AdapterUtils
import Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types
import Hydra.Dsl.Tests

import Hydra.TestData
import Hydra.TestUtils

import qualified Test.Hspec as H
import qualified Data.Map as M
import qualified Test.QuickCheck as QC
import qualified Data.Set as S
import qualified Data.Maybe as Y


constraintsAreAsExpected :: H.SpecWith ()
constraintsAreAsExpected = H.describe "Verify that the language constraints include/exclude the appropriate types" $ do

    H.it "int16 and int32 are supported in the test context" $ do
      typeIsSupported (context [TypeVariantLiteral]) Types.int16 `H.shouldBe` True
      typeIsSupported (context [TypeVariantLiteral]) Types.int32 `H.shouldBe` True

    H.it "int8 and bigint are unsupported in the test context" $ do
      typeIsSupported (context [TypeVariantLiteral]) Types.int8 `H.shouldBe` False
      typeIsSupported (context [TypeVariantLiteral]) Types.bigint `H.shouldBe` False

    H.it "Records are supported, but unions are not" $ do
      typeIsSupported (context [TypeVariantLiteral, TypeVariantRecord]) testTypeLatLon `H.shouldBe` True
      typeIsSupported (context [TypeVariantLiteral, TypeVariantRecord]) stringOrIntType `H.shouldBe` False

    H.it "Records are supported if and only if each of their fields are supported" $ do
      typeIsSupported (context [TypeVariantLiteral, TypeVariantRecord])
        (TypeRecord $ RowType (Name "Example") Nothing [Types.field "first" Types.string, Types.field "second" Types.int16])
        `H.shouldBe` True
      typeIsSupported (context [TypeVariantLiteral, TypeVariantRecord])
        (TypeRecord $ RowType (Name "Example") Nothing [Types.field "first" Types.string, Types.field "second" Types.int8])
        `H.shouldBe` False

    H.it "Lists are supported if the list element type is supported" $ do
      typeIsSupported (context [TypeVariantLiteral, TypeVariantList]) listOfStringsType `H.shouldBe` True
      typeIsSupported (context [TypeVariantLiteral, TypeVariantList]) listOfListsOfStringsType `H.shouldBe` True
      typeIsSupported (context [TypeVariantLiteral, TypeVariantList]) listOfSetOfStringsType `H.shouldBe` False

  where
    context = languageConstraints . adapterContextLanguage . termTestContext

supportedConstructorsAreUnchanged :: H.SpecWith ()
supportedConstructorsAreUnchanged = H.describe "Verify that supported term constructors are unchanged" $ do

  H.it "Strings (and other supported literal values) pass through without change" $
    QC.property $ \b -> checkDataAdapter
      [TypeVariantLiteral]
      Types.string
      Types.string
      False
      (string b)
      (string b)

  H.it "Lists (when supported) pass through without change" $
    QC.property $ \strings -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantList]
      listOfStringsType
      listOfStringsType
      False
      (list $ string <$> strings)
      (list $ string <$> strings)

  H.it "Maps (when supported) pass through without change" $
    QC.property $ \keyvals -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantMap]
      mapOfStringsToIntsType
      mapOfStringsToIntsType
      False
      (makeMap keyvals)
      (makeMap keyvals)

  H.it "Optionals (when supported) pass through without change" $
    QC.property $ \mi -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantOptional]
      optionalInt8Type
      optionalInt16Type
      False
      (optional $ int8 <$> mi)
      (optional $ int16 . fromIntegral <$> mi)

  H.it "Records (when supported) pass through without change" $
    QC.property $ \a1 a2 -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantRecord]
      (TypeRecord $ RowType testTypeName Nothing [Types.field "first" Types.string, Types.field "second" Types.int8])
      (TypeRecord $ RowType testTypeName Nothing [Types.field "first" Types.string, Types.field "second" Types.int16])
      False
      (record testTypeName [field "first" $ string a1, field "second" $ int8 a2])
      (record testTypeName [field "first" $ string a1, field "second" $ int16 $ fromIntegral a2])

  H.it "Unions (when supported) pass through without change" $
    QC.property $ \int -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantUnion]
      stringOrIntType
      stringOrIntType
      False
      (variant stringOrIntName (FieldName "right") $ int32 int)
      (variant stringOrIntName (FieldName "right") $ int32 int)

  H.it "Sets (when supported) pass through without change" $
    QC.property $ \strings -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantSet]
      setOfStringsType
      setOfStringsType
      False
      (stringSet strings)
      (stringSet strings)

  H.it "Primitive function references (when supported) pass through without change" $
    QC.property $ \name -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantFunction]
      concatType
      concatType
      False
      (primitive name)
      (primitive name)

  H.it "Projections (when supported) pass through without change" $
    QC.property $ \fname -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantFunction, TypeVariantRecord]
      exampleProjectionType
      exampleProjectionType
      False
      (project testTypePersonName fname)
      (project testTypePersonName fname)

unsupportedConstructorsAreModified :: H.SpecWith ()
unsupportedConstructorsAreModified = H.describe "Verify that unsupported term constructors are changed in the expected ways" $ do

  H.it "Sets (when unsupported) become lists" $
    QC.property $ \strings -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantList]
      setOfStringsType
      listOfStringsType
      False
      (stringSet strings)
      (stringList $ S.toList strings)

  H.it "Optionals (when unsupported) become lists" $
    QC.property $ \ms -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantList]
      (Types.optional Types.string)
      (Types.list Types.string)
      False
      (optional $ string <$> ms)
      (list $ Y.maybe [] (\s -> [string s]) ms)

  H.it "Primitive function references (when unsupported) become variant terms" $
    QC.property $ \name -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantUnion, TypeVariantRecord]
      concatType
      (functionProxyType Types.string)
      False
      (primitive name)
      (inject functionProxyName $ field "primitive" $ string $ unName name) -- Note: the function name is not dereferenced

  H.it "Projections (when unsupported) become variant terms" $
    QC.property $ \fname -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantUnion, TypeVariantRecord]
      exampleProjectionType
      (functionProxyType testTypePerson)
      False
      (project testTypePersonName fname)
      (inject functionProxyName $ field "record" $ string $
        show (project testTypePersonName fname :: Term)) -- Note: the field name is not dereferenced

  H.it "Unions (when unsupported) become records" $
    QC.property $ \i -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantOptional, TypeVariantRecord]
      eitherStringOrInt8Type
      (TypeRecord $ RowType eitherStringOrInt8TypeName Nothing [
        Types.field "left" $ Types.optional Types.string,
        Types.field "right" $ Types.optional Types.int16])
      False
      (inject eitherStringOrInt8TypeName $ field "right" $ int8 i)
      (record eitherStringOrInt8TypeName [
        field "left" $ optional Nothing,
        field "right" $ optional $ Just $ int16 $ fromIntegral i])

termsAreAdaptedRecursively :: H.SpecWith ()
termsAreAdaptedRecursively = H.describe "Verify that the adapter descends into subterms and transforms them appropriately" $ do

  H.it "A list of int8's becomes a list of int32's" $
    QC.property $ \ints -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantList]
      listOfInt8sType
      listOfInt16sType
      False
      (list $ int8 <$> ints)
      (list $ int16 . fromIntegral <$> ints)

  H.it "A list of sets of strings becomes a list of lists of strings" $
    QC.property $ \lists -> checkDataAdapter
      [TypeVariantLiteral, TypeVariantList]
      listOfSetOfStringsType
      listOfListsOfStringsType
      False
      (list $ (\l -> set $ S.fromList $ string <$> l) <$> lists)
      (list $ (\l -> list $ string <$> S.toList (S.fromList l)) <$> lists)

roundTripsPreserveSelectedTypes :: H.SpecWith ()
roundTripsPreserveSelectedTypes = H.describe "Verify that the adapter is information preserving, i.e. that round-trips are no-ops" $ do

  H.it "Check strings (pass-through)" $
    QC.property $ \s -> roundTripIsNoop Types.string (string s)

  H.it "Check lists (pass-through)" $
    QC.property $ \strings -> roundTripIsNoop listOfStringsType (list $ string <$> strings)

  H.it "Check sets (which map to lists)" $
    QC.property $ \strings -> roundTripIsNoop setOfStringsType (stringSet strings)

  H.it "Check primitive function references (which map to variants)" $
    QC.property $ \name -> roundTripIsNoop concatType (primitive name)

  H.it "Check projection terms (which map to variants)" $
    QC.property $ \fname -> roundTripIsNoop exampleProjectionType (project testTypePersonName fname)

  H.it "Check nominally typed terms (which pass through as instances of the aliased type)" $
    QC.property $ \s -> roundTripIsNoop testTypeStringAlias (wrap testTypeStringAliasName $ string s)

--roundTripsPreserveArbitraryTypes :: H.SpecWith ()
--roundTripsPreserveArbitraryTypes = H.describe "Verify that the adapter is information preserving for arbitrary typed terms" $ do
--
--  H.it "Check arbitrary type/term pairs" $
--    QC.property $ \(TypedTerm typ term) -> roundTripIsNoop typ term

fieldAdaptersAreAsExpected :: H.SpecWith ()
fieldAdaptersAreAsExpected = H.describe "Check that field adapters are as expected" $ do

  H.it "An int8 field becomes an int16 field" $
    QC.property $ \i -> checkFieldAdapter
      [TypeVariantLiteral, TypeVariantRecord]
      (Types.field "second" Types.int8)
      (Types.field "second" Types.int16)
      False
      (field "second" $ int8 i)
      (field "second" $ int16 $ fromIntegral i)

roundTripIsNoop :: Type -> Term -> H.Expectation
roundTripIsNoop typ term = shouldSucceedWith
   (step coderEncode term >>= step coderDecode)
   term
  where
    step = adapt typ

    -- Use a YAML-like language (but supporting unions) as the default target language
    testLanguage = Language (LanguageName "hydra/test") $ LanguageConstraints {
      languageConstraintsEliminationVariants = S.empty, -- S.fromList eliminationVariants,
      languageConstraintsLiteralVariants = S.fromList [
        LiteralVariantBoolean, LiteralVariantFloat, LiteralVariantInteger, LiteralVariantString],
      languageConstraintsFloatTypes = S.fromList [FloatTypeBigfloat],
      languageConstraintsFunctionVariants = S.empty,
      languageConstraintsIntegerTypes = S.fromList [IntegerTypeBigint],
      languageConstraintsTermVariants = S.fromList termVariants,
      languageConstraintsTypeVariants = S.fromList [
        TypeVariantAnnotated, TypeVariantLiteral, TypeVariantList, TypeVariantMap, TypeVariantRecord, TypeVariantUnion],
      languageConstraintsTypes = \typ -> case stripType typ of
        TypeOptional (TypeOptional _) -> False
        _ -> True }

    -- Note: in a real application, you wouldn't create the adapter just to use it once;
    --       it should be created once, then applied to many terms.
    adapt typ dir term = do
      adapter <- languageAdapter testLanguage typ
      dir (adapterCoder adapter) term

spec :: H.Spec
spec = do
  constraintsAreAsExpected
  supportedConstructorsAreUnchanged
  unsupportedConstructorsAreModified
  termsAreAdaptedRecursively
  roundTripsPreserveSelectedTypes
--  roundTripsPreserveArbitraryTypes -- TODO: restore me
  fieldAdaptersAreAsExpected
