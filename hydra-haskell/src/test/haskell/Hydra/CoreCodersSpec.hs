module Hydra.CoreCodersSpec where

import Hydra.Kernel
import Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import Hydra.TestData
import Hydra.TestUtils
import Hydra.ArbitraryCore (untyped)

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.Map as M


checkAnnotationsArePreserved :: H.SpecWith ()
checkAnnotationsArePreserved = do
  H.describe "Check that metadata is preserved through a type-encoding round trip" $ do

    H.it "Basic metadata" $ do
      shouldSucceedWith
        (coreDecodeType $ coreEncodeType annotatedStringType)
        annotatedStringType
  where
    annotatedStringType :: Type
    annotatedStringType = TypeAnnotated $ Annotated Types.string $ M.fromList [
      (annotationKey_description, Terms.string "The string literal type"),
      (annotationKey_type, coreEncodeType $ TypeVariable _Type)]

checkDecodingIndividualTypes :: H.SpecWith ()
checkDecodingIndividualTypes = do
  H.describe "Individual decoder test cases" $ do

    H.it "float32 literal type" $ do
      shouldSucceedWith
        (coreDecodeLiteralType
          (variant _LiteralType _LiteralType_float $ unitVariant _FloatType _FloatType_float32))
        (LiteralTypeFloat FloatTypeFloat32)

    H.it "float32 type" $ do
      shouldSucceedWith
        (coreDecodeType
          (variant _Type _Type_literal $ variant _LiteralType _LiteralType_float $ unitVariant _FloatType _FloatType_float32))
        Types.float32

    H.it "union type" $ do
      shouldSucceedWith
        (coreDecodeType $
          variant _Type _Type_union $ record _RowType [
            Field _RowType_typeName $ wrap _Name $ string (unName testTypeName),
            Field _RowType_extends $ optional Nothing,
            Field _RowType_fields $
              list [
                record _FieldType [
                  Field _FieldType_name $ wrap _FieldName $ string "left",
                  Field _FieldType_type $ variant _Type _Type_literal $ variant _LiteralType _LiteralType_integer $
                    unitVariant _IntegerType _IntegerType_int64],
                record _FieldType [
                  Field _FieldType_name $ wrap _FieldName $ string "right",
                  Field _FieldType_type $ variant _Type _Type_literal $ variant _LiteralType _LiteralType_float $
                    unitVariant _FloatType _FloatType_float64]]])
          (TypeUnion $ RowType testTypeName Nothing [
            Types.field "left" Types.int64,
            Types.field "right" Types.float64])

checkDecodingInvalidTerms :: H.SpecWith ()
checkDecodingInvalidTerms = do
  H.describe "Decode invalid terms" $ do

    H.it "Try to decode a term with wrong fields for Type" $ do
      shouldFail (coreDecodeType $ variant untyped (FieldName "unknownField") $ list [])

    H.it "Try to decode an incomplete representation of a Type" $ do
      shouldFail (coreDecodeType $ variant _Type _Type_literal $ unitVariant _LiteralType _LiteralType_integer)

checkEncodingIndividualTypes :: H.SpecWith ()
checkEncodingIndividualTypes = do
  H.describe "Individual encoder test cases" $ do

    H.it "string literal type" $ do
      H.shouldBe
        (strip $ coreEncodeLiteralType LiteralTypeString :: Term)
        (strip $ unitVariant _LiteralType _LiteralType_string)

    H.it "string type" $ do
      H.shouldBe
        (strip $ coreEncodeType Types.string :: Term)
        (strip $ variant _Type _Type_literal (unitVariant _LiteralType _LiteralType_string))

    H.it "int32 type" $ do
      H.shouldBe
        (strip $ coreEncodeType Types.int32 :: Term)
        (strip $ variant _Type _Type_literal (variant _LiteralType _LiteralType_integer $ unitVariant _IntegerType _IntegerType_int32))

    H.it "record type" $ do
      H.shouldBe
        (strip $ coreEncodeType (TypeRecord $ RowType (Name "Example") Nothing
          [Types.field "something" Types.string, Types.field "nothing" Types.unit]) :: Term)
        (strip $ variant _Type _Type_record $
          record _RowType [
            Field _RowType_typeName $ wrap _Name $ string "Example",
            Field _RowType_extends $ optional Nothing,
            Field _RowType_fields $ list [
              record _FieldType [
                Field _FieldType_name $ wrap _FieldName $ string "something",
                Field _FieldType_type $ variant _Type _Type_literal $ unitVariant _LiteralType _LiteralType_string],
              record _FieldType [
                Field _FieldType_name $ wrap _FieldName $ string "nothing",
                Field _FieldType_type $ variant _Type _Type_record $ record _RowType [
                  Field _RowType_typeName $ wrap _Name $ string "hydra/core.UnitType",
                  Field _RowType_extends $ optional Nothing,
                  Field _RowType_fields $ list []]]]])

checkRoundTripsFromMonomorphicTypes :: H.SpecWith ()
checkRoundTripsFromMonomorphicTypes = do
  H.describe "Check that encoding, then decoding randomly generated monomorphic types is a no-op" $

    H.it "Try random types" $ QC.property roundTripSucceeds

checkRoundTripsFromPolymorphicTypes :: H.SpecWith ()
checkRoundTripsFromPolymorphicTypes = do
  -- Note: type generation does not yet support polymorphic types
  H.describe "Check that encoding, then decoding individual polymorphic types is a no-op" $ do

      H.it "Try unbound type variables" $ roundTripSucceeds $
        Types.var "MyType"

      H.it "Try function types with unbound type variables" $ roundTripSucceeds $
        Types.function (Types.var "a") (Types.var "b")

      H.describe "Try 'forall' (lambda) types" $ do
        H.it "test #1" $ roundTripSucceeds $
          Types.lambda "a" $ Types.list $ Types.var "a"
        H.it "test #2" $ roundTripSucceeds $
          Types.lambda "a" $ Types.lambda "b" $ Types.function (Types.var "a") (Types.var "b")
        -- Note: we do not test type lambdas in subtypes (except on the left hand side of applications),
        --       as these are not meaningful in Hydra

      H.describe "Try type applications" $ do
        H.it "test #1" $ roundTripSucceeds $
          Types.apply (Types.var "Type1") (Types.var "Type2")
        H.it "test #2" $ roundTripSucceeds $
          Types.apply (Types.apply (Types.var "Type1") (Types.var "Type2")) (Types.var "Type3")
        H.it "test #3" $ roundTripSucceeds $
          Types.apply (Types.apply (Types.var "Type1") (Types.var "Type1")) (Types.var "Type1")
        H.it "test #4" $ roundTripSucceeds $
          Types.apply (Types.lambda "a" $ Types.list $ Types.var "a") Types.int32

roundTripSucceeds :: Type -> H.Expectation
roundTripSucceeds typ = shouldSucceedWith (coreDecodeType $ coreEncodeType typ) typ

spec :: H.Spec
spec = do
  checkAnnotationsArePreserved
  checkDecodingIndividualTypes
  checkDecodingInvalidTerms
  checkEncodingIndividualTypes
  checkRoundTripsFromMonomorphicTypes
  checkRoundTripsFromPolymorphicTypes
