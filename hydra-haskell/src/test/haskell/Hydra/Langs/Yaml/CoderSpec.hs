module Hydra.Langs.Yaml.CoderSpec where

import Hydra.Kernel
import Hydra.Dsl.Terms
import Hydra.Langs.Yaml.Coder
import qualified Hydra.Langs.Yaml.Model as YM
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
literalTypeConstraintsAreRespected = H.describe "Verify that YAML's literal type constraints are respected" $ do

  -- TODO: binary data

  H.it "Check booleans" $
    QC.property $ \b -> checkYamlCoder Types.boolean (boolean b) (yamlBool b)

  H.it "Check 32-bit floats" $
    QC.property $ \f -> checkYamlCoder Types.float32 (float32 f) (yamlFloat $ realToFrac f)

  H.it "Check 64-bit floats (doubles)" $
    QC.property $ \d -> checkYamlCoder Types.float64 (float64 d) (yamlFloat $ realToFrac d)

  -- TODO: bigfloat

  H.it "Check 32-bit integers" $
    QC.property $ \i -> checkYamlCoder Types.int32 (int32 i) (yamlInt i)

  H.it "Check 16-bit unsigned integers" $
    QC.property $ \i -> checkYamlCoder Types.uint16 (uint16 i) (yamlInt i)

  H.it "Check arbitrary-precision integers" $
    QC.property $ \i -> checkYamlCoder Types.bigint (bigint i) (yamlInt i)

  H.it "Check strings" $
    QC.property $ \s -> checkYamlCoder Types.string (string s) (yamlStr s)

supportedTypesPassThrough :: H.SpecWith ()
supportedTypesPassThrough = H.describe "Verify that supported types are mapped directly" $ do

  H.it "Lists become YAML sequences" $
    QC.property $ \strings -> checkYamlCoder listOfStringsType
      (list $ string <$> strings) (YM.NodeSequence $ yamlStr <$> strings)

  H.it "Maps become YAML mappings" $
    QC.property $ \keyvals -> checkYamlCoder mapOfStringsToIntsType
      (makeMap keyvals) (yamlMap $ BF.bimap yamlStr yamlInt <$> keyvals)

  H.it "Optionals become YAML null or type-specific nodes" $
    QC.property $ \ms -> checkYamlCoder optionalStringType
      (optional $ string <$> ms) (YM.NodeScalar $ Y.maybe YM.ScalarNull YM.ScalarStr ms)

  H.it "Records become YAML mappings" $
    QC.property $ \lat lon -> checkYamlCoder latLonType
      (latlonRecord lat lon) (yamlMap [
        (yamlStr "lat", yamlFloat $ realToFrac lat),
        (yamlStr "lon", yamlFloat $ realToFrac lon)])

unsupportedTypesAreTransformed :: H.SpecWith ()
unsupportedTypesAreTransformed = H.describe "Verify that unsupported types are transformed appropriately" $ do

  -- TODO: functions

  H.it "Sets become sequences" $
    QC.property $ \strings -> checkYamlCoder setOfStringsType
      (stringSet strings) (YM.NodeSequence $ yamlStr <$> S.toList strings)

  H.it "Nominal types are dereferenced" $
    QC.property $ \s -> checkYamlCoder stringAliasType
      (wrap stringAliasTypeName $ string s) (yamlStr s)

  H.it "Unions become YAML mappings (as records)" $
    QC.property $ \int -> checkYamlCoder stringOrIntType
      (variant stringOrIntName (FieldName "right") $ int32 int)
      (yamlMap [(yamlStr "right", yamlInt int)])

spec :: H.Spec
spec = do
  literalTypeConstraintsAreRespected
  supportedTypesPassThrough
  unsupportedTypesAreTransformed

checkYamlCoder :: Type -> Term -> YM.Node -> H.Expectation
checkYamlCoder typ term node = case mstep of
    Nothing -> HL.assertFailure (traceSummary trace)
    Just step -> do
      shouldSucceedWith (coderEncode step term) node
      shouldSucceedWith (coderEncode step term >>= coderDecode step) term
  where
    FlowState mstep _ trace = unFlow (yamlCoder typ) testGraph emptyTrace

yamlBool :: Bool -> YM.Node
yamlBool = YM.NodeScalar . YM.ScalarBool

yamlFloat :: Double -> YM.Node
yamlFloat = YM.NodeScalar . YM.ScalarFloat

yamlInt :: Integral i => i -> YM.Node
yamlInt = YM.NodeScalar . YM.ScalarInt . fromIntegral

yamlMap :: [(YM.Node, YM.Node)] -> YM.Node
yamlMap = YM.NodeMapping . M.fromList

yamlNull :: YM.Node
yamlNull = YM.NodeScalar YM.ScalarNull

yamlStr :: String -> YM.Node
yamlStr = YM.NodeScalar . YM.ScalarStr
