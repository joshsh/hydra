module Hydra.Ext.Haskell.Language where

import Hydra.Adapter
import Hydra.Basics
import Hydra.Core

import qualified Data.Set as S


haskellLanguage :: Language m
haskellLanguage = Language (LanguageName "hydra/ext/haskell") $ LanguageConstraints {
  languageConstraintsLiteralVariants = S.fromList [
    LiteralVariantBoolean, LiteralVariantFloat, LiteralVariantInteger, LiteralVariantString],
  languageConstraintsFloatTypes = S.fromList [
    -- Bigfloat is excluded for now
    FloatTypeFloat32,
    FloatTypeFloat64],
  languageConstraintsFunctionVariants = S.fromList functionVariants,
  languageConstraintsIntegerTypes = S.fromList [IntegerTypeBigint, IntegerTypeInt32],
  languageConstraintsDataVariants = S.fromList [
    DataVariantApplication,
    DataVariantElement,
    DataVariantFunction,
    DataVariantList,
    DataVariantLiteral,
    DataVariantMap,
    DataVariantNominal,
    DataVariantOptional,
    DataVariantRecord,
    DataVariantSet,
    DataVariantUnion,
    DataVariantVariable],
  languageConstraintsTypeVariants = S.fromList [
    TypeVariantElement,
    TypeVariantFunction,
    TypeVariantList,
    TypeVariantLiteral,
    TypeVariantMap,
    TypeVariantNominal,
    TypeVariantOptional,
    TypeVariantRecord,
    TypeVariantSet,
    TypeVariantUnion,
    TypeVariantUniversal,
    TypeVariantVariable],
  languageConstraintsTypes = const True }

haskellReservedWords :: S.Set String
haskellReservedWords = S.fromList preludeSymbols
  where
    -- See: https://www.haskell.org/onlinereport/standard-prelude.html
    -- List created on 2022-06-01. Symbols not containing at least one alphanumeric character are excluded.
    preludeSymbols = [
      "Bool", "Bounded", "Char", "Double", "EQ", "Either", "Enum", "Eq", "False", "Float", "Floating", "Fractional",
      "Functor", "GT", "IO", "Int", "Integer", "Integral", "Just", "LT", "Left", "Maybe", "Monad", "Nothing", "Num",
      "Ord", "Ordering", "Rational", "Real", "RealFloat", "RealFrac", "Right", "String", "True", "abs", "acos", "acosh",
      "asTypeOf", "asin", "asinh", "atan", "atan2", "atanh", "ceiling", "compare", "const", "cos", "cosh", "curry",
      "decodeFloat", "div", "divMod", "either", "encodeFloat", "enumFrom", "enumFromThen", "enumFromThenTo",
      "enumFromTo", "error", "even", "exp", "exponent", "fail", "flip", "floatDigits", "floatRadix", "floatRange",
      "floor", "fmap", "fromEnum", "fromInteger", "fromIntegral", "fromRational", "fst", "gcd", "id", "isDenormalized",
      "isIEEE", "isInfinite", "isNaN", "isNegativeZero", "lcm", "log", "logBase", "mapM", "mapM_", "max", "maxBound",
      "maybe", "min", "minBound", "mod", "negate", "not", "odd", "otherwise", "pi", "pred", "properFraction", "quot",
      "quotRem", "realToFrac", "recip", "rem", "return", "round", "scaleFloat", "seq", "sequence", "sequence_",
      "significand", "signum", "sin", "sinh", "snd", "sqrt", "subtract", "succ", "tan", "tanh", "toEnum", "toInteger",
      "toRational", "truncate", "uncurry", "undefined", "until"]
