module Hydra.TestData where

import Hydra.Kernel
import Hydra.Dsl.Terms
import Hydra.TestGraph
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Data.Map as M


concatType :: Type Kv
concatType = Types.function Types.string $ Types.function Types.string Types.string

compareStringsType :: Type Kv
compareStringsType = Types.function Types.string Types.string

eitherStringOrInt8Type :: Type Kv
eitherStringOrInt8Type = TypeUnion $ RowType eitherStringOrInt8TypeName Nothing
  [Types.field "left" Types.string, Types.field "right" Types.int8]

eitherStringOrInt8TypeName :: Name
eitherStringOrInt8TypeName = unqualifyName $ QualifiedName (Just testNamespace) "EitherStringOrInt8"

exampleProjectionType :: Type Kv
exampleProjectionType = Types.function testTypePerson Types.string

listOfInt8sType :: Type Kv
listOfInt8sType = Types.list Types.int8

listOfInt16sType :: Type Kv
listOfInt16sType = Types.list Types.int16

listOfListsOfStringsType :: Type Kv
listOfListsOfStringsType = Types.list $ Types.list Types.string

listOfSetOfStringsType :: Type Kv
listOfSetOfStringsType = Types.list $ Types.set Types.string

listOfStringsType :: Type Kv
listOfStringsType = Types.list Types.string

makeMap :: [(String, Int)] -> Term
makeMap keyvals = Terms.map $ M.fromList $ ((\(k, v) -> (string k, int32 v)) <$> keyvals)

mapOfStringsToIntsType :: Type Kv
mapOfStringsToIntsType = Types.map Types.string Types.int32

optionalInt8Type :: Type Kv
optionalInt8Type = Types.optional Types.int8

optionalInt16Type :: Type Kv
optionalInt16Type = Types.optional Types.int16

optionalStringType :: Type Kv
optionalStringType = Types.optional Types.string

setOfStringsType :: Type Kv
setOfStringsType = Types.set Types.string

stringOrIntName :: Name
stringOrIntName = Name "StringOrInt"

stringOrIntType :: Type Kv
stringOrIntType = TypeUnion $ RowType stringOrIntName Nothing [Types.field "left" Types.string, Types.field "right" Types.int32]

testTypeName :: Name
testTypeName = unqualifyName $ QualifiedName (Just testNamespace) "TestType"
