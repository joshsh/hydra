module Hydra.Langs.Shacl.Language where

import Hydra.Kernel

import qualified Data.Set as S


shaclLanguage :: Language
shaclLanguage = Language (LanguageName "hydra/langs/shacl") $ LanguageConstraints {
  languageConstraintsEliminationVariants = S.empty,
  languageConstraintsLiteralVariants = S.fromList literalVariants,
  languageConstraintsFloatTypes = S.fromList floatTypes,
  languageConstraintsFunctionVariants = S.empty,
  languageConstraintsIntegerTypes = S.fromList integerTypes,
  languageConstraintsTermVariants = S.fromList [
    TermVariantList,
    TermVariantLiteral,
    TermVariantMap,
    TermVariantWrap,
    TermVariantOptional,
    TermVariantRecord,
    TermVariantSet,
    TermVariantUnion],
  languageConstraintsTypeVariants = S.fromList [
    TypeVariantAnnotated,
    TypeVariantList,
    TypeVariantLiteral,
    TypeVariantMap,
    TypeVariantWrap,
    TypeVariantOptional,
    TypeVariantRecord,
    TypeVariantSet,
    TypeVariantUnion],
  languageConstraintsTypes = const True }
