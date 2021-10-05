module Hydra.Ext.Yaml.AdapterSpec where

import Hydra.Core
import Hydra.Evaluation
import Hydra.Graph
import Hydra.Translation
import Hydra.Prototyping.Basics
import Hydra.Prototyping.Helpers
import Hydra.Prototyping.Primitives
import Hydra.Prototyping.Steps
import qualified Hydra.Ext.Yaml.Adapter as YA
import qualified Hydra.Ext.Yaml.Coder as YC

import Hydra.ArbitraryCore
import Hydra.TestGraph

import qualified Test.Hspec as H
import qualified Data.Char as C
import qualified Data.Either as E
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Test.QuickCheck as QC


yamlTestContext = TranslationContext testContext hydraCoreLanguage YC.yamlLanguage
  
-- Note: in a real application, you wouldn't create the adapter just to use it once;
--       it should be created once, then applied to many terms.
adapt typ dir term = do
  adapter <- YA.termAdapter yamlTestContext typ
  dir adapter term

booleanElementType = TypeElement $ TypeAtomic AtomicTypeBoolean
booleanElementDataType = functionType booleanElementType booleanType
concatType = functionType stringType $ functionType stringType stringType
compareStringsType = functionType stringType stringType
exampleProjectionType = functionType latLonType int64Type
latLonType = TypeRecord [FieldType "lat" $ int64Type, FieldType "lon" $ int64Type]
listOfSetOfStringsType = TypeList $ TypeSet stringType
listOfStringsType = TypeList stringType
latlonRecord lat lon = TermRecord [Field "lat" $ int32Value lat, Field "lon" $ int32Value lon]
makeMap keyvals = TermMap $ M.fromList $ ((\(k, v) -> (stringValue k, int32Value v)) <$> keyvals)
mapOfStringsToIntsType = mapType stringType int32Type
setOfStringsType = TypeSet stringType
stringAliasType = TypeNominal "StringTypeAlias"
stringList strings = TermList $ stringValue <$> strings
stringOrIntType = TypeUnion [FieldType "left" stringType, FieldType "right" int32Type]
stringSet strings = TermSet $ S.fromList $ stringValue <$> (S.toList strings)

supportedConstructorsAreUnchanged = do
  H.describe "Verify that supported term constructors are unchanged" $ do
    
    H.it "Strings (and other supported atomic values) pass through without change" $
      QC.property $ \s
        -> adapt stringType stepOut (stringValue s)
        == Right (stringValue s)  

    H.it "Lists pass through without change" $
      QC.property $ \strings
        -> adapt listOfStringsType stepOut (TermList $ stringValue <$> strings)
        == Right (TermList $ stringValue <$> strings)  
        
    H.it "Maps pass through without change" $
      QC.property $ \keyvals
        -> adapt mapOfStringsToIntsType stepOut (makeMap keyvals)
        == Right (makeMap keyvals)  
        
    H.it "Records pass through without change" $
      QC.property $ \(lat, lon)
        -> adapt latLonType stepOut (latlonRecord lat lon)
        == Right (latlonRecord lat lon)

    H.it "Unions pass through without change" $
      QC.property $ \int
        -> adapt stringOrIntType stepOut (variant "right" int)
        == Right (variant "right" int)
        
unsupportedConstructorsAreModified = do
  H.describe "Verify that unsupported term constructors are changed in the expected ways" $ do

    H.it "Sets become lists" $
      QC.property $ \strings
        -> adapt setOfStringsType stepOut (stringSet strings)
        == Right (stringList $ S.toList strings)  

    H.it "Element references become strings" $
      QC.property $ \name
        -> adapt booleanElementType stepOut (TermElement name) -- Note: the element name is not dereferenced
        == Right (stringValue name)  

    H.it "CompareTo terms become variant terms" $
      QC.property $ \s
        -> adapt compareStringsType stepOut (TermCompareTo $ stringValue s)
        == Right (TermUnion $ Field "compareTo" $ stringValue s)  

    H.it "Data terms become variant terms" $ do
      adapt booleanElementDataType stepOut TermData
      `H.shouldBe` Right (TermUnion $ Field "data" unitTerm)  

    H.it "Primitive function references become variant terms" $
      QC.property $ \name
        -> adapt concatType stepOut (TermFunction name)  -- Note: the function name is not dereferenced
        == Right (TermUnion $ Field "function" $ stringValue name)  

    H.it "Projections become variant terms" $ do
      QC.property $ \fname
        -> adapt exampleProjectionType stepOut (TermProjection fname) -- Note: the field name is not dereferenced
        == Right (TermUnion $ Field "projection" $ stringValue fname)  

nominalTypesPassThrough = do
  H.describe "Verify that nominal types behave like the types they reference" $ do

    H.it "A term typed by StringTypeAlias just behaves like a string" $
      QC.property $ \s
        -> adapt stringAliasType stepOut (stringValue s)
        == Right (stringValue s)

termsAreAdaptedRecursively = do
  H.describe "Verify that the adapter descends into subterms and transforms them appropriately" $ do

    H.it "A list of sets of strings becomes a list of lists of strings" $ do
      QC.property $ \lists
        -> adapt listOfSetOfStringsType stepOut (TermList $ (\l -> TermSet $ S.fromList $ stringValue <$> l) <$> lists)
        == Right (TermList $ (\l -> TermList $ stringValue <$> (S.toList $ S.fromList l)) <$> lists)

adapterIsInformationPreserving = do
  H.describe "Verify that the adapter is information preserving, i.e. that round-trips are no-ops" $ do

    H.it "Check strings (pass-through)" $
      QC.property $ \s -> roundTripIsNoop stringType (stringValue s)
          
    H.it "Check lists (pass-through)" $
      QC.property $ \strings -> roundTripIsNoop listOfStringsType (TermList $ stringValue <$> strings)

    H.it "Check sets (which map to lists)" $
      QC.property $ \strings -> roundTripIsNoop setOfStringsType (stringSet strings)

    H.it "Check element references (which map to strings)" $
      QC.property $ \name -> roundTripIsNoop booleanElementType (TermElement name)

    H.it "Check compareTo terms (which map to variants)" $
      QC.property $ \s -> roundTripIsNoop compareStringsType (TermCompareTo $ stringValue s)

    H.it "Check data terms (which map to variants)" $
      roundTripIsNoop booleanElementDataType TermData `H.shouldBe` True

    H.it "Check primitive function references (which map to variants)" $
      QC.property $ \name -> roundTripIsNoop concatType (TermFunction name)

    H.it "Check projection terms (which map to variants)" $
      QC.property $ \fname -> roundTripIsNoop exampleProjectionType (TermProjection fname)

    H.it "Check nominally typed terms (which pass through as instances of the aliased type)" $
      QC.property $ \s -> roundTripIsNoop stringAliasType (stringValue s)

  where
    roundTripIsNoop typ term = (adapter stepOut term >>= adapter stepIn) == Right term
      where
        adapter = adapt typ

spec :: H.Spec
spec = do
  supportedConstructorsAreUnchanged
  unsupportedConstructorsAreModified
  nominalTypesPassThrough
  termsAreAdaptedRecursively
  adapterIsInformationPreserving
