module Hydra.Langs.Graphql.Language where

import Hydra.Kernel

import qualified Data.List as L
import qualified Data.Set as S


graphqlLanguage :: Language
graphqlLanguage = Language (LanguageName "hydra/langs/graphql") $ LanguageConstraints {
  -- Note: this language is for schemas and data only; support for queries may be added later
  languageConstraintsEliminationVariants = S.empty,
  languageConstraintsLiteralVariants = S.fromList [
    LiteralVariantBoolean, -- Boolean
    LiteralVariantFloat,   -- Float
    LiteralVariantInteger, -- Int
    LiteralVariantString], -- String
  languageConstraintsFloatTypes = S.fromList [
    FloatTypeFloat64], -- Float
  languageConstraintsFunctionVariants = S.empty,
  languageConstraintsIntegerTypes = S.fromList [
    IntegerTypeInt32], -- Int
  languageConstraintsTermVariants = S.fromList [
    TermVariantList,
    TermVariantLiteral,
    TermVariantOptional,
    TermVariantRecord,
    TermVariantUnion], -- Unions are supported only in the form of enums
  languageConstraintsTypeVariants = S.fromList [
    TypeVariantList,
    TypeVariantLiteral,
    TypeVariantWrap,
    TypeVariantOptional,
    TypeVariantRecord,
    TypeVariantUnion, -- Unions are supported only in the form of enums
    TypeVariantVariable],
  languageConstraintsTypes = \typ -> case stripType typ of
    -- If it is a union type, make sure it can be treated as an enum.
    TypeUnion rt -> L.foldl (\b f -> b && isEnumField f) True $ rowTypeFields rt
      where
        isUnitType t = case stripType t of
          TypeRecord (RowType name _ fields) -> L.null fields || name == _UnitType
          _ -> False
        isEnumField = isUnitType . fieldTypeType
    TypeOptional et -> case stripType et of
      TypeOptional _ -> False  -- No encoding for optionals within optionals
      _ -> True
    _ -> True}

graphqlReservedWords :: S.Set String
graphqlReservedWords = S.fromList ["true", "false"]
