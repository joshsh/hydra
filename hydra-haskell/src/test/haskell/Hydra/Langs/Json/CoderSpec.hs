module Hydra.Langs.Json.CoderSpec where

import Hydra.Kernel
import Hydra.Lib.Literals
import Hydra.Langs.Json.Coder
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Json as Json
import qualified Hydra.Dsl.Types as Types
import Hydra.Dsl.Tests

import Hydra.TestData
import Hydra.TestUtils

import qualified Data.Bifunctor as BF
import qualified Test.Hspec as H
import qualified Test.HUnit.Lang as HL
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y
import qualified Test.QuickCheck as QC


literalTypeConstraintsAreRespected :: H.SpecWith ()
literalTypeConstraintsAreRespected = H.describe "Verify that JSON's literal type constraints are respected" $ do

  -- TODO: binary data

  H.it "Check booleans" $
    QC.property $ \b -> checkJsonCoder Types.boolean (Terms.boolean b) (Json.ValueBoolean b)

  H.it "Check 32-bit floats" $
    QC.property $ \f -> checkJsonCoder Types.float32 (Terms.float32 f) (jsonFloat $ realToFrac f)

  H.it "Check 64-bit floats (doubles)" $
    QC.property $ \d -> checkJsonCoder Types.float64 (Terms.float64 d) (jsonFloat $ realToFrac d)

  -- TODO: bigfloat

  H.it "Check 32-bit integers" $
    QC.property $ \i -> checkJsonCoder Types.int32 (Terms.int32 i) (jsonInt i)

  H.it "Check 16-bit unsigned integers" $
    QC.property $ \i -> checkJsonCoder Types.uint16 (Terms.uint16 i) (jsonInt i)

  H.it "Check arbitrary-precision integers" $
    QC.property $ \i -> checkJsonCoder Types.bigint (Terms.bigint i) (jsonInt i)

  H.it "Check strings" $
    QC.property $ \s -> checkJsonCoder Types.string (Terms.string s) (Json.ValueString s)

supportedTypesPassThrough :: H.SpecWith ()
supportedTypesPassThrough = H.describe "Verify that supported types are mapped directly" $ do

  H.it "Lists become JSON arrays" $
    QC.property $ \strings -> checkJsonCoder listOfStringsType
      (Terms.list $ Terms.string <$> strings) (Json.ValueArray $ Json.ValueString <$> strings)

  H.it "Maps become JSON objects" $
    QC.property $ \keyvals -> checkJsonCoder mapOfStringsToIntsType
      (makeMap keyvals) (jsonMap $ BF.bimap id jsonInt <$> keyvals)

  H.it "Optionals become JSON null or type-specific values" $
    QC.property $ \ms -> checkJsonCoder optionalStringType
      (Terms.optional $ Terms.string <$> ms) (Y.maybe Json.ValueNull Json.ValueString ms)

  H.it "Records become JSON objects" $
    QC.property $ \lat lon -> checkJsonCoder latLonType
      (latlonRecord lat lon) (jsonMap [
        ("lat", jsonFloat $ realToFrac lat),
        ("lon", jsonFloat $ realToFrac lon)])

unsupportedTypesAreTransformed :: H.SpecWith ()
unsupportedTypesAreTransformed = H.describe "Verify that unsupported types are transformed appropriately" $ do

  -- TODO: functions

  H.it "Sets become arrays" $
    QC.property $ \strings -> checkJsonCoder setOfStringsType
      (stringSet strings)
      (Json.ValueArray $ Json.ValueString <$> S.toList strings)

  H.it "Nominal types are dereferenced" $
    QC.property $ \s -> checkJsonCoder stringAliasType
      (Terms.wrap stringAliasTypeName $ Terms.string s)
      (Json.ValueString s)

  H.it "Unions become JSON objects (as records)" $
    QC.property $ \int -> checkJsonCoder stringOrIntType
      (Terms.inject stringOrIntName $ Field (FieldName "right") $ Terms.int32 int)
      (jsonMap [("right", jsonInt int)])

wrappedTypesAreSupported :: H.SpecWith ()
wrappedTypesAreSupported = H.describe "Verify that nominal types are supported" $ do
  H.it "Nominal unions become single-attribute objects" $
    QC.property $ \() -> checkJsonCoder (TypeVariable testTypeFoobarValueName)
      (Terms.inject testTypeFoobarValueName $ Terms.field "bool" $ Terms.boolean True)
      (jsonMap [("bool", jsonBool True)])

  H.it "Nominal enums become single-attribute objects with empty-object values, and type annotations are transparent" $
    QC.property $ \() -> checkJsonCoder (TypeVariable testTypeComparisonName)
      (Terms.inject testTypeComparisonName $ Terms.field "equalTo" Terms.unit)
      (jsonMap [("equalTo", jsonMap [])])

spec :: H.Spec
spec = do
  literalTypeConstraintsAreRespected
  supportedTypesPassThrough
  unsupportedTypesAreTransformed
  wrappedTypesAreSupported

checkJsonCoder :: Type -> Term -> Json.Value -> H.Expectation
checkJsonCoder typ term node = case mstep of
    Nothing -> HL.assertFailure (traceSummary trace)
    Just step -> do
      shouldSucceedWith (coderEncode step term) node
      shouldSucceedWith (coderEncode step term >>= coderDecode step) term
  where
    FlowState mstep _ trace = unFlow (jsonCoder typ) testGraph emptyTrace

jsonBool :: Bool -> Json.Value
jsonBool = Json.ValueBoolean

jsonFloat :: Double -> Json.Value
jsonFloat = Json.ValueNumber

jsonInt :: Integral i => i -> Json.Value
jsonInt = Json.ValueNumber . bigintToBigfloat . fromIntegral

jsonMap :: [(String, Json.Value)] -> Json.Value
jsonMap = Json.ValueObject . M.fromList
