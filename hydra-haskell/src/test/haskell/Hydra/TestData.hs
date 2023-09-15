module Hydra.TestData where

import Hydra.Kernel
import Hydra.Dsl.Terms
import Hydra.TestGraph
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Data.Map as M


concatType :: Type
concatType = Types.function Types.string $ Types.function Types.string Types.string

compareStringsType :: Type
compareStringsType = Types.function Types.string Types.string

eitherStringOrInt8Type :: Type
eitherStringOrInt8Type = TypeUnion $ RowType eitherStringOrInt8TypeName Nothing
  [Types.field "left" Types.string, Types.field "right" Types.int8]

eitherStringOrInt8TypeName :: Name
eitherStringOrInt8TypeName = unqualifyName $ QualifiedName (Just testNamespace) "EitherStringOrInt8"

exampleProjectionType :: Type
exampleProjectionType = Types.function testTypePerson Types.string

listOfInt8sType :: Type
listOfInt8sType = Types.list Types.int8

listOfInt16sType :: Type
listOfInt16sType = Types.list Types.int16

listOfListsOfStringsType :: Type
listOfListsOfStringsType = Types.list $ Types.list Types.string

listOfSetOfStringsType :: Type
listOfSetOfStringsType = Types.list $ Types.set Types.string

listOfStringsType :: Type
listOfStringsType = Types.list Types.string

makeMap :: [(String, Int)] -> Term
makeMap keyvals = Terms.map $ M.fromList $ ((\(k, v) -> (string k, int32 v)) <$> keyvals)

mapOfStringsToIntsType :: Type
mapOfStringsToIntsType = Types.map Types.string Types.int32

optionalInt8Type :: Type
optionalInt8Type = Types.optional Types.int8

optionalInt16Type :: Type
optionalInt16Type = Types.optional Types.int16

optionalStringType :: Type
optionalStringType = Types.optional Types.string

setOfStringsType :: Type
setOfStringsType = Types.set Types.string

stringOrIntName :: Name
stringOrIntName = Name "StringOrInt"

stringOrIntType :: Type
stringOrIntType = TypeUnion $ RowType stringOrIntName Nothing [Types.field "left" Types.string, Types.field "right" Types.int32]

testTypeName :: Name
testTypeName = unqualifyName $ QualifiedName (Just testNamespace) "TestType"
