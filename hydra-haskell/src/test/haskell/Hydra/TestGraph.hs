module Hydra.TestGraph (
  module Hydra.TestGraph,
  module Hydra.Sources.Libraries,
) where

import Hydra.Kernel
import Hydra.Sources.Libraries
import Hydra.Sources.Core
import Hydra.Dsl.Annotations as Ann
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Terms
import qualified Hydra.Dsl.Types as Types

import qualified Data.Map  as M
import qualified Data.Set  as S
import qualified Hydra.Dsl.Terms as Terms


testTypeLatLonName :: Name
testTypeLatLonName = Name "LatLon"

testTypeLatLonPolyName :: Name
testTypeLatLonPolyName = Name "LatLonPoly"

latlonRecord :: Float -> Float -> Term
latlonRecord lat lon = record testTypeLatLonName [
  Field (Name "lat") $ float32 lat,
  Field (Name "lon") $ float32 lon]

testTypeLatLon :: Type
testTypeLatLon = TypeRecord $ RowType testTypeLatLonName Nothing [
  Types.field "lat" Types.float32,
  Types.field "lon" Types.float32]

testTypeLatLonPolyType :: Type
testTypeLatLonPolyType = TypeLambda $ LambdaType (Name "a") $
  TypeRecord $ RowType testTypeLatLonPolyName Nothing [
    Types.field "lat" $ Types.var "a",
    Types.field "lon" $ Types.var "a"]

testTypeSimpleNumberName :: Name
testTypeSimpleNumberName = Name "SimpleNumber"

testTypeSimpleNumber :: Type
testTypeSimpleNumber = TypeUnion $ RowType testTypeSimpleNumberName Nothing [
  Types.field "int" Types.int32,
  Types.field "float" Types.float32]

testTypeStringAlias :: Type
testTypeStringAlias = Ann.doc "An alias for the string type" $
  TypeWrap $ Nominal testTypeStringAliasName Types.string

testTypeStringAliasName :: Name
testTypeStringAliasName = Name "StringTypeAlias"

testElementArthur :: Element
testElementArthur = Element {
  elementName = Name "ArthurDent",
  elementData = testDataArthur}

testElementFirstName :: Element
testElementFirstName = Element {
  elementName = Name "firstName",
  elementData = project testTypePersonName $ Name "firstName"}

testGraph :: Graph
testGraph = elementsToGraph hydraCore (Just testSchemaGraph) [testElementArthur, testElementFirstName]

testNamespace :: Namespace
testNamespace = Namespace "testGraph"

testSchemaGraph :: Graph
testSchemaGraph = elementsToGraph hydraCore (Just hydraCore) [
    def testTypeBuddyListAName testTypeBuddyListA,
    def testTypeBuddyListBName testTypeBuddyListB,
    def testTypeComparisonName testTypeComparison,
    def testTypeIntListName testTypeIntList,
    def testTypeHydraLiteralTypeName testTypeHydraLiteralType,
    def testTypeHydraTypeName testTypeHydraType,
    def testTypeLatLonName testTypeLatLon,
    def testTypeLatLonPolyName testTypeLatLonPolyType,
    def testTypeListName testTypeList,
    def testTypeNumberName testTypeNumber,
    def testTypePersonName testTypePerson,
    def testTypePersonOrSomethingName testTypePersonOrSomething,
    def testTypeSimpleNumberName testTypeSimpleNumber,
    def testTypeStringAliasName testTypeStringAlias,
    def testTypeTimestampName testTypeTimestamp,
    def testTypeUnionMonomorphicName testTypeUnionMonomorphic,
    def testTypeUnionPolymorphicRecursiveName testTypeUnionPolymorphicRecursive]
  where
    def = typeDefinitionElement

testSchemaNamespace :: Namespace
testSchemaNamespace = Namespace "testSchemaGraph"

testDataArthur :: Term
testDataArthur = record testTypePersonName [
  "firstName">: string "Arthur",
  "lastName">: string "Dent",
  "age">: int32 42]

testTypeBuddyListA :: Type
testTypeBuddyListA = Types.lambda "a" $ TypeRecord $ RowType testTypeBuddyListAName Nothing [
  Types.field "head" $ Types.var "a",
  Types.field "tail" $ Types.optional $ Types.apply (TypeVariable testTypeBuddyListBName) (Types.var "a")]

testTypeBuddyListAName :: Name
testTypeBuddyListAName = Name "BuddyListA"

testTypeBuddyListB :: Type
testTypeBuddyListB = Types.lambda "a" $ TypeRecord $ RowType testTypeBuddyListBName Nothing [
  Types.field "head" $ Types.var "a",
  Types.field "tail" $ Types.optional $ Types.apply (TypeVariable testTypeBuddyListAName) (Types.var "a")]

testTypeBuddyListBName :: Name
testTypeBuddyListBName = Name "BuddyListB"

testTypeComparison :: Type
testTypeComparison = TypeUnion $ RowType testTypeComparisonName Nothing [
  Types.field "lessThan" Types.unit,
  Types.field "equalTo" Types.unit,
  Types.field "greaterThan" Types.unit]

testTypeComparisonName :: Name
testTypeComparisonName = Name "Comparison"

testTypeIntList :: Type
testTypeIntList = TypeRecord $ RowType testTypeIntListName Nothing [
  Types.field "head" $ Types.int32,
  Types.field "tail" $ Types.optional $ TypeVariable testTypeIntListName]

testTypeIntListName :: Name
testTypeIntListName = Name "IntList"

testTypeHydraLiteralType :: Type
testTypeHydraLiteralType = Ann.doc "An approximation of Hydra's LiteralType type" $
  TypeUnion $ RowType testTypeHydraLiteralTypeName Nothing [
--    Types.field "boolean" Types.unit,
--    Types.field "string" Types.unit]
    Types.field "boolean" Types.string,
    Types.field "string" Types.string]

testTypeHydraLiteralTypeName :: Name
testTypeHydraLiteralTypeName = Name "HydraLiteralType"

testTypeHydraType :: Type
testTypeHydraType = Ann.doc "An approximation of Hydra's Type type" $
  TypeUnion $ RowType testTypeHydraTypeName Nothing [
    Types.field "literal" $ TypeVariable testTypeHydraLiteralTypeName,
    Types.field "list" $ TypeVariable testTypeHydraTypeName]

testTypeHydraTypeName :: Name
testTypeHydraTypeName = Name "HydraType"

testTypeList :: Type
testTypeList = Types.lambda "a" $ TypeRecord $ RowType testTypeListName Nothing [
  Types.field "head" $ Types.var "a",
  Types.field "tail" $ Types.optional $ Types.apply (TypeVariable testTypeListName) (Types.var "a")]

testTypeListName :: Name
testTypeListName = Name "List"

testTypeNumber :: Type
testTypeNumber = TypeUnion $ RowType testTypeNumberName Nothing [
  Types.field "int" Types.int32,
  Types.field "float" Types.float32]

testTypeNumberName :: Name
testTypeNumberName = Name "Number"

testTypePerson :: Type
testTypePerson = TypeRecord $ RowType testTypePersonName Nothing [
  Types.field "firstName" Types.string,
  Types.field "lastName" Types.string,
  Types.field "age" Types.int32]

testTypePersonName :: Name
testTypePersonName = Name "Person"

testTypePersonOrSomething :: Type
testTypePersonOrSomething = Types.lambda "a" $ TypeUnion $ RowType testTypePersonOrSomethingName Nothing [
  Types.field "person" testTypePerson,
  Types.field "other" $ Types.var "a"]

testTypePersonOrSomethingName :: Name
testTypePersonOrSomethingName = Name "PersonOrSomething"

testTypeTimestamp :: Type
testTypeTimestamp = TypeUnion $ RowType testTypeTimestampName Nothing [
  FieldType (Name "unixTimeMillis") Types.uint64,
  FieldType (Name "date") Types.string]

testTypeTimestampName :: Name
testTypeTimestampName = Name "Timestamp"

testTypeUnionMonomorphic :: Type
testTypeUnionMonomorphic = TypeUnion $ RowType testTypeUnionMonomorphicName Nothing [
  Types.field "bool" Types.boolean,
  Types.field "string" Types.string,
  Types.field "unit" Types.unit]

testTypeUnionMonomorphicName :: Name
testTypeUnionMonomorphicName = Name "UnionMonomorphic"

testTypeUnionPolymorphicRecursive :: Type
testTypeUnionPolymorphicRecursive = Types.lambda "a" $ TypeUnion $ RowType testTypeUnionPolymorphicRecursiveName Nothing [
  Types.field "bool" Types.boolean,
  Types.field "value" $ Types.var "a",
  Types.field "other" $ Types.apply (TypeVariable testTypeUnionPolymorphicRecursiveName) (Types.var "a")]

testTypeUnionPolymorphicRecursiveName :: Name
testTypeUnionPolymorphicRecursiveName = Name "UnionPolymorphicRecursive"
