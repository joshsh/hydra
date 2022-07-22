module Hydra.Ext.Json.Language where

import Hydra.Core
import Hydra.Adapter
import Hydra.Common
import Hydra.Evaluation

import qualified Data.Set as S


language :: Context m -> Language m
language cx = Language (LanguageName "hydra/ext/json") $ LanguageConstraints {
  languageConstraintsEliminationVariants = S.empty,
  languageConstraintsLiteralVariants = S.fromList [
    LiteralVariantBoolean, LiteralVariantFloat, LiteralVariantInteger, LiteralVariantString],
  languageConstraintsFloatTypes = S.fromList [FloatTypeBigfloat],
  languageConstraintsFunctionVariants = S.empty,
  languageConstraintsIntegerTypes = S.fromList [IntegerTypeBigint],
  languageConstraintsTermVariants = S.fromList [
    TermVariantLiteral,
    TermVariantList,
    TermVariantMap,
    TermVariantOptional,
    TermVariantRecord],
  languageConstraintsTypeVariants = S.fromList [
    TypeVariantAnnotated, TypeVariantLiteral, TypeVariantList, TypeVariantMap, TypeVariantOptional, TypeVariantRecord],
  languageConstraintsTypes = \typ -> case typeExpr cx typ of
    TypeOptional (TypeOptional _) -> False
    _ -> True }
