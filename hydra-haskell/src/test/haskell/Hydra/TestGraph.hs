module Hydra.TestGraph (
  module Hydra.TestGraph,
  module Hydra.Sources.Libraries,
) where

import Hydra.Kernel
import Hydra.Sources.Libraries
import Hydra.Dsl.Terms
import Hydra.Sources.Core
import Hydra.Dsl.Annotations as Ann
import Hydra.Dsl.Bootstrap
import qualified Hydra.Dsl.Types as Types

import qualified Data.Map  as M
import qualified Data.Set  as S
import qualified Hydra.Dsl.Terms as Terms


latLonName :: Name
latLonName = Name "LatLon"

latLonPolyName :: Name
latLonPolyName = Name "LatLonPoly"

latlonRecord :: Float -> Float -> Term Kv
latlonRecord lat lon = record latLonName [Field (FieldName "lat") $ float32 lat, Field (FieldName "lon") $ float32 lon]

latLonType :: Type Kv
latLonType = TypeRecord $ RowType latLonName Nothing [Types.field "lat" Types.float32, Types.field "lon" Types.float32]

latLonPolyType :: Type Kv
latLonPolyType = TypeLambda $ LambdaType (Name "a") $
  TypeRecord $ RowType latLonPolyName Nothing [Types.field "lat" $ Types.var "a", Types.field "lon" $ Types.var "a"]

stringAliasType :: Type Kv
stringAliasType = TypeWrap $ Nominal stringAliasTypeName Types.string

stringAliasTypeName :: Name
stringAliasTypeName = Name "StringTypeAlias"

testElementArthur :: Element Kv
testElementArthur = Element {
  elementName = Name "ArthurDent",
  elementData = testDataArthur}

testElementFirstName :: Element Kv
testElementFirstName = Element {
  elementName = Name "firstName",
  elementData = project testTypePersonName $ FieldName "firstName"}

testGraph :: Graph Kv
testGraph = elementsToGraph hydraCore (Just testSchemaGraph) [testElementArthur, testElementFirstName]

testNamespace :: Namespace
testNamespace = Namespace "testGraph"

testSchemaGraph :: Graph Kv
testSchemaGraph = elementsToGraph hydraCore (Just hydraCore) [
    def stringAliasTypeName $ Ann.doc "An alias for the string type" stringAliasType,
    def testTypeFoobarValueName testTypeFoobarValue,
    def testTypeNumberName testTypeNumber,
    def testTypeComparisonName testTypeComparison,
    def latLonName latLonType,
    def latLonPolyName latLonPolyType,
    def testTypePersonName testTypePerson,
    def testTypePersonOrSomethingName testTypePersonOrSomething,
    def testTypeTimestampName testTypeTimestamp]
  where
    def = typeElement

testSchemaNamespace :: Namespace
testSchemaNamespace = Namespace "testSchemaGraph"

testDataArthur :: Term Kv
testDataArthur = record testTypePersonName [
  Field (FieldName "firstName") $ string "Arthur",
  Field (FieldName "lastName") $ string "Dent",
  Field (FieldName "age") $ int32 42]

testTypeComparison :: Type Kv
testTypeComparison = TypeUnion $ RowType testTypeComparisonName Nothing [
  Types.field "lessThan" Types.unit,
  Types.field "equalTo" Types.unit,
  Types.field "greaterThan" Types.unit]

testTypeComparisonName :: Name
testTypeComparisonName = Name "Comparison"

testTypeFoobarValue :: Type Kv
testTypeFoobarValue = TypeUnion $ RowType testTypeFoobarValueName Nothing [
  Types.field "bool" Types.boolean,
  Types.field "string" Types.string,
  Types.field "unit" Types.unit]

testTypeFoobarValueName :: Name
testTypeFoobarValueName = Name "FoobarValue"

testTypeNumber :: Type Kv
testTypeNumber = TypeUnion $ RowType testTypeNumberName Nothing [
  Types.field "int" Types.int32,
  Types.field "float" Types.float32]

testTypeNumberName :: Name
testTypeNumberName = Name "Number"

testTypePerson :: Type Kv
testTypePerson = TypeRecord $ RowType testTypePersonName Nothing [
  Types.field "firstName" Types.string,
  Types.field "lastName" Types.string,
  Types.field "age" Types.int32]

testTypePersonName :: Name
testTypePersonName = Name "Person"

testTypePersonOrSomething :: Type Kv
testTypePersonOrSomething = Types.lambda "a" $ TypeUnion $ RowType testTypePersonOrSomethingName Nothing [
  Types.field "person" testTypePerson,
  Types.field "other" $ Types.var "a"]

testTypePersonOrSomethingName :: Name
testTypePersonOrSomethingName = Name "PersonOrSomething"

testTypeTimestamp :: Type Kv
testTypeTimestamp = TypeUnion $ RowType testTypeTimestampName Nothing [
  FieldType (FieldName "unixTimeMillis") Types.uint64,
  FieldType (FieldName "date") Types.string]

testTypeTimestampName :: Name
testTypeTimestampName = Name "Timestamp"
