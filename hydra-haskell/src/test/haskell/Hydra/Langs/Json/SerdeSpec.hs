-- Note: these tests are dependent on Data.Aeson, both because the Serde depends on Data.Aeson
--       and because of the particular serialization style.

module Hydra.Langs.Json.SerdeSpec where

import Hydra.Kernel
import Hydra.Dsl.Terms
import Hydra.Langs.Json.Serde
import qualified Hydra.Dsl.Types as Types

import Hydra.TestData
import Hydra.TestUtils

import qualified Test.Hspec as H
import qualified Data.List as L
import qualified Test.QuickCheck as QC
import qualified Data.Maybe as Y


checkLiterals :: H.SpecWith ()
checkLiterals = H.describe "Test literal values" $ do

  H.it "Booleans become 'true' and 'false'" $ do
    QC.property $ \b -> checkSerialization jsonStringCoder
      (TypedTerm Types.boolean $ boolean b)
      (if b then "true" else "false")

  H.it "int32's become numbers, and are serialized in the obvious way" $ do
    QC.property $ \i -> checkSerialization jsonStringCoder
      (TypedTerm Types.int32 $ int32 i)
      (show i)

  H.it "uint8's and other finite integer types become numbers, and are serialized in the obvious way" $ do
    QC.property $ \i -> checkSerialization jsonStringCoder
      (TypedTerm Types.uint8 $ uint8 i)
      (show i)

  H.it "bigints become numbers" $ do
    QC.property $ \i -> checkSerialization jsonStringCoder
      (TypedTerm Types.bigint $ bigint i)
      (show i)

checkOptionals :: H.SpecWith ()
checkOptionals = H.describe "Test and document serialization of optionals" $ do

  H.it "A 'nothing' becomes 'null' (except when it appears as a field)" $
    QC.property $ \mi -> checkSerialization jsonStringCoder
      (TypedTerm
        (Types.optional Types.int32)
        (optional $ (Just . int32) =<< mi))
      (Y.maybe "null" show mi)

  H.it "Nested optionals case #1: just x? :: optional<optional<int32>>" $
    QC.property $ \mi -> checkSerialization jsonStringCoder
      (TypedTerm
        (Types.optional $ Types.optional Types.int32)
        (optional $ Just $ optional $ (Just . int32) =<< mi))
      ("[" ++ Y.maybe "null" show mi ++ "]")

  H.it "Nested optionals case #2: nothing :: optional<optional<int32>>" $
    QC.property $ \() -> checkSerialization jsonStringCoder
      (TypedTerm
        (Types.optional $ Types.optional Types.int32)
        (optional Nothing))
      "[]"

checkRecordsAndUnions :: H.SpecWith ()
checkRecordsAndUnions = H.describe "Test and document handling of optionals vs. nulls for record and union types" $ do

  H.it "Empty records become empty objects" $
    QC.property $ \() -> checkSerialization jsonStringCoder
      (TypedTerm Types.unit unit)
      "{}"

  H.it "Simple records become simple objects" $
    QC.property $ \() -> checkSerialization jsonStringCoder
      (TypedTerm testTypeLatLon (latlonRecord 37 (negate 122)))
      "{\"lat\":37,\"lon\":-122}"

  H.it "Optionals are omitted from record objects if 'nothing'" $
    QC.property $ \() -> checkSerialization jsonStringCoder
      (TypedTerm
        (TypeRecord $ RowType testTypeName Nothing [Types.field "one" $ Types.optional Types.string, Types.field "two" $ Types.optional Types.int32])
        (record testTypeName [Field (FieldName "one") $ optional $ Just $ string "test", Field (FieldName "two") $ optional Nothing]))
      "{\"one\":\"test\"}"

  H.it "Simple unions become simple objects, via records" $
    QC.property $ \() -> checkSerialization jsonStringCoder
      (TypedTerm
        (TypeUnion $ RowType testTypeName Nothing [Types.field "left" Types.string, Types.field "right" Types.int32])
        (inject testTypeName $ Field (FieldName "left") $ string "test"))
      "{\"left\":\"test\"}"

jsonByteStringCoderIsInformationPreserving :: H.SpecWith ()
jsonByteStringCoderIsInformationPreserving = H.describe "Verify that a round trip from a type+term, to serialized JSON, and back again is a no-op" $ do

  H.it "Generate arbitrary type/term pairs, serialize the terms to JSON, deserialize them, and compare" $
    QC.property (checkSerdeRoundTrip jsonByteStringCoder)

spec :: H.Spec
spec = do
  checkLiterals
  checkOptionals
  checkRecordsAndUnions
--  jsonByteStringCoderIsInformationPreserving -- TODO: restore me
