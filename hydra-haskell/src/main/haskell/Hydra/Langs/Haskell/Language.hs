module Hydra.Langs.Haskell.Language where

import Hydra.Kernel

import qualified Data.Set as S


haskellLanguage :: Language
haskellLanguage = Language (LanguageName "hydra/langs/haskell") $ LanguageConstraints {
  languageConstraintsEliminationVariants = S.fromList eliminationVariants,
  languageConstraintsLiteralVariants = S.fromList [
    LiteralVariantBoolean,
    LiteralVariantFloat,
    LiteralVariantInteger,
    LiteralVariantString],
  languageConstraintsFloatTypes = S.fromList [
    -- Bigfloat is excluded for now
    FloatTypeFloat32, -- Float
    FloatTypeFloat64], -- Double
  languageConstraintsFunctionVariants = S.fromList functionVariants,
  languageConstraintsIntegerTypes = S.fromList [
    IntegerTypeBigint, -- Integer
    IntegerTypeInt8, -- Int8
    IntegerTypeInt16, -- Int16
    IntegerTypeInt32, -- Int
    IntegerTypeInt64], -- Int64
  languageConstraintsTermVariants = S.fromList [
    TermVariantApplication,
    TermVariantFunction,
    TermVariantLet,
    TermVariantList,
    TermVariantLiteral,
    TermVariantMap,
    TermVariantOptional,
    TermVariantProduct,
    TermVariantRecord,
    TermVariantSet,
    TermVariantUnion,
    TermVariantVariable,
    TermVariantWrap],
  languageConstraintsTypeVariants = S.fromList [
    TypeVariantAnnotated,
    TypeVariantApplication,
    TypeVariantFunction,
    TypeVariantLambda,
    TypeVariantList,
    TypeVariantLiteral,
    TypeVariantMap,
    TypeVariantOptional,
    TypeVariantProduct,
    TypeVariantRecord,
    TypeVariantSet,
    TypeVariantUnion,
    TypeVariantVariable,
    TypeVariantWrap],
  languageConstraintsTypes = const True }

reservedWords :: S.Set String
reservedWords = S.fromList $ preludeSymbols ++ extSymbols
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
    -- Additional symbols which need to be reserved, as the Haskell coder uses them in their unqualified form
    extSymbols = ["Map", "Set"]
