module Hydra.Langs.Scala.Language where

import Hydra.Kernel

import qualified Data.Set as S


scalaLanguage :: Language
scalaLanguage = Language (LanguageName "hydra/langs/scala") $ LanguageConstraints {
  languageConstraintsEliminationVariants = S.fromList eliminationVariants,
  languageConstraintsLiteralVariants = S.fromList [
    LiteralVariantBoolean,
    LiteralVariantFloat,
    LiteralVariantInteger,
    LiteralVariantString],
  languageConstraintsFloatTypes = S.fromList [
    -- Bigfloat is excluded for now
    FloatTypeFloat32,
    FloatTypeFloat64],
  languageConstraintsFunctionVariants = S.fromList functionVariants,
  languageConstraintsIntegerTypes = S.fromList [
    IntegerTypeBigint,
    IntegerTypeInt16,
    IntegerTypeInt32,
    IntegerTypeInt64,
    IntegerTypeUint8],
  languageConstraintsTermVariants = S.fromList [
    TermVariantApplication,
    TermVariantFunction,
    TermVariantList,
    TermVariantLiteral,
    TermVariantMap,
    TermVariantOptional,
    TermVariantRecord,
    TermVariantSet,
    TermVariantUnion,
    TermVariantVariable,
    TermVariantWrap],
  languageConstraintsTypeVariants = S.fromList [
    TypeVariantAnnotated,
    TypeVariantFunction,
    TypeVariantList,
    TypeVariantLiteral,
    TypeVariantMap,
    TypeVariantOptional,
    TypeVariantRecord,
    TypeVariantSet,
    TypeVariantUnion,
    TypeVariantLambda,
    TypeVariantVariable,
    TypeVariantWrap],
  languageConstraintsTypes = const True }

reservedWords :: S.Set [Char]
reservedWords = S.fromList $ keywords ++ classNames
  where
    -- Classes in the Scala Standard Library 2.13.8
    -- Note: numbered class names like Function1, Product16, and the names of exception/error classes are omitted,
    --       as they are unlikely to occur by chance.
    classNames = [
      "Any", "AnyVal", "App", "Array", "Boolean", "Byte", "Char", "Console", "DelayedInit", "Double", "DummyExplicit",
      "Dynamic", "Enumeration", "Equals", "Float", "Function", "Int", "Long", "MatchError", "None",
      "Nothing", "Null", "Option", "PartialFunction", "Predef", "Product", "Proxy",
      "SerialVersionUID", "Short", "Singleton", "Some", "Specializable", "StringContext",
      "Symbol", "Unit", "ValueOf"]
    -- Not an official or comprehensive list; taken from https://www.geeksforgeeks.org/scala-keywords
    keywords = [
      "abstract", "case", "catch", "class", "def", "do", "else", "extends", "false", "final", "finally", "for",
      "forSome", "if", "implicit", "import", "lazy", "match", "new", "null", "object", "override", "package", "private",
      "protected", "return", "sealed", "super", "this", "throw", "trait", "true", "try", "type", "val", "var", "while",
      "with", "yield"]
