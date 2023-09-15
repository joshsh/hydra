-- | Utilities for use in transformations

module Hydra.Printing where

import qualified Hydra.Basics as Basics
import qualified Hydra.Core as Core
import qualified Hydra.Lib.Literals as Literals
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Mantle as Mantle
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | Display a floating-point type as a string
describeFloatType :: (Core.FloatType -> String)
describeFloatType t = (Strings.cat [
  (\x -> describePrecision (Basics.floatTypePrecision x)) t,
  " floating-point numbers"])

-- | Display an integer type as a string
describeIntegerType :: (Core.IntegerType -> String)
describeIntegerType t = (Strings.cat [
  (\x -> describePrecision (Basics.integerTypePrecision x)) t,
  " integers"])

-- | Display a literal type as a string
describeLiteralType :: (Core.LiteralType -> String)
describeLiteralType x = case x of
  Core.LiteralTypeBinary -> "binary strings"
  Core.LiteralTypeBoolean -> "boolean values"
  Core.LiteralTypeFloat v -> (describeFloatType v)
  Core.LiteralTypeInteger v -> (describeIntegerType v)
  Core.LiteralTypeString -> "character strings"

-- | Display numeric precision as a string
describePrecision :: (Mantle.Precision -> String)
describePrecision x = case x of
  Mantle.PrecisionArbitrary -> "arbitrary-precision"
  Mantle.PrecisionBits v -> (Strings.cat [
    Literals.showInt32 v,
    "-bit"])

-- | Display a type as a string
describeType :: (Core.Type -> String)
describeType x = case x of
  Core.TypeAnnotated v -> (Strings.cat [
    "annotated ",
    (describeType (Core.annotatedSubject v))])
  Core.TypeApplication _ -> "instances of an application type"
  Core.TypeLiteral v -> (describeLiteralType v)
  Core.TypeFunction v -> (Strings.cat [
    Strings.cat [
      Strings.cat [
        "functions from ",
        (describeType (Core.functionTypeDomain v))],
      " to "],
    (describeType (Core.functionTypeCodomain v))])
  Core.TypeLambda _ -> "polymorphic terms"
  Core.TypeList v -> (Strings.cat [
    "lists of ",
    (describeType v)])
  Core.TypeMap v -> (Strings.cat [
    Strings.cat [
      Strings.cat [
        "maps from ",
        (describeType (Core.mapTypeKeys v))],
      " to "],
    (describeType (Core.mapTypeValues v))])
  Core.TypeOptional v -> (Strings.cat [
    "optional ",
    (describeType v)])
  Core.TypeProduct _ -> "tuples"
  Core.TypeRecord _ -> "records"
  Core.TypeSet v -> (Strings.cat [
    "sets of ",
    (describeType v)])
  Core.TypeStream v -> (Strings.cat [
    "streams of ",
    (describeType v)])
  Core.TypeSum _ -> "variant tuples"
  Core.TypeUnion _ -> "unions"
  Core.TypeVariable _ -> "instances of a named type"
  Core.TypeWrap v -> (Strings.cat [
    "wrapper for ",
    (describeType (Core.nominalObject v))])
