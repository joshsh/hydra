module Hydra.Langs.Tinkerpop.Language where

import Hydra.Kernel
import Hydra.Langs.Tinkerpop.Features

import qualified Data.Set as S
import qualified Data.Maybe as Y


-- Populate language constraints based on TinkerPop Graph.Features.
-- Note: although Graph.Features is phrased such that it defaults to supporting features not explicitly mentioned,
--       for Hydra we cannot support a term or type pattern unless it is provably safe in the target environment.
--       Otherwise, generated expressions could cause failure during runtime operations.
-- Also note that extra features are required on top of Graph.Features, again for reasons of completeness.
tinkerpopLanguage :: LanguageName -> Features -> ExtraFeatures a -> Language Kv
tinkerpopLanguage name features extras = Language name $ LanguageConstraints {
    languageConstraintsEliminationVariants = S.empty,

    languageConstraintsLiteralVariants = S.fromList $ Y.catMaybes [
      -- Binary values map to byte arrays. Lists of uint8 also map to byte arrays.
      cond LiteralVariantBinary (dataTypeFeaturesSupportsByteArrayValues vpFeatures),
      cond LiteralVariantBoolean (dataTypeFeaturesSupportsBooleanValues vpFeatures),
      cond LiteralVariantFloat (dataTypeFeaturesSupportsFloatValues vpFeatures
        || dataTypeFeaturesSupportsDoubleValues vpFeatures),
      cond LiteralVariantInteger (dataTypeFeaturesSupportsIntegerValues vpFeatures
        || dataTypeFeaturesSupportsLongValues vpFeatures),
      cond LiteralVariantString (dataTypeFeaturesSupportsStringValues vpFeatures)],

    languageConstraintsFloatTypes = S.fromList $ Y.catMaybes [
      cond FloatTypeFloat32 (dataTypeFeaturesSupportsFloatValues vpFeatures),
      cond FloatTypeFloat64 (dataTypeFeaturesSupportsDoubleValues vpFeatures)],

    languageConstraintsFunctionVariants = S.empty,

    languageConstraintsIntegerTypes = S.fromList $ Y.catMaybes [
      cond IntegerTypeInt32 (dataTypeFeaturesSupportsIntegerValues vpFeatures),
      cond IntegerTypeInt64 (dataTypeFeaturesSupportsLongValues vpFeatures)],

    -- Only lists and literal values may be explicitly supported via Graph.Features.
    languageConstraintsTermVariants = S.fromList $ Y.catMaybes [
      cond TermVariantList supportsLists,
      cond TermVariantLiteral supportsLiterals,
      cond TermVariantMap supportsMaps,
      -- An optional value translates to an absent vertex property
      Just TermVariantOptional],

    languageConstraintsTypeVariants = S.fromList $ Y.catMaybes [
      cond TypeVariantList supportsLists,
      cond TypeVariantLiteral supportsLiterals,
      cond TypeVariantMap supportsMaps,
      Just TypeVariantOptional,
      Just TypeVariantWrap],

    languageConstraintsTypes = \typ -> case stripType typ of
      -- Only lists of literal values are supported, as nothing else is mentioned in Graph.Features
      TypeList t -> case stripType t of
        TypeLiteral lt -> case lt of
          LiteralTypeBoolean -> dataTypeFeaturesSupportsBooleanArrayValues vpFeatures
          LiteralTypeFloat ft -> case ft of
            FloatTypeFloat64 -> dataTypeFeaturesSupportsDoubleArrayValues vpFeatures
            FloatTypeFloat32 -> dataTypeFeaturesSupportsFloatArrayValues vpFeatures
            _ -> False
          LiteralTypeInteger it -> case it of
             IntegerTypeUint8 -> dataTypeFeaturesSupportsByteArrayValues vpFeatures
             IntegerTypeInt32 -> dataTypeFeaturesSupportsIntegerArrayValues vpFeatures
             IntegerTypeInt64 -> dataTypeFeaturesSupportsLongArrayValues vpFeatures
             _ -> False
          LiteralTypeString -> dataTypeFeaturesSupportsStringArrayValues vpFeatures
          _ -> False
        _ -> False
      TypeLiteral _ -> True
      TypeMap (MapType kt _) -> extraFeaturesSupportsMapKey extras kt
      TypeWrap _ -> True
      TypeOptional ot -> case stripType ot of
        TypeLiteral _ -> True
        _ -> False
      _ -> True}

  where
    cond v b = if b then Just v else Nothing

    vpFeatures = vertexPropertyFeaturesDataTypeFeatures $ vertexFeaturesProperties $ featuresVertex features

    supportsLists = dataTypeFeaturesSupportsBooleanArrayValues vpFeatures
      || dataTypeFeaturesSupportsByteArrayValues vpFeatures
      || dataTypeFeaturesSupportsDoubleArrayValues vpFeatures
      || dataTypeFeaturesSupportsFloatArrayValues vpFeatures
      || dataTypeFeaturesSupportsIntegerArrayValues vpFeatures
      || dataTypeFeaturesSupportsLongArrayValues vpFeatures
      || dataTypeFeaturesSupportsStringArrayValues vpFeatures

      -- Support for at least one of the Graph.Features literal types is assumed.
    supportsLiterals = True

    -- Note: additional constraints are required, beyond Graph.Features, if maps are supported
    supportsMaps = dataTypeFeaturesSupportsMapValues vpFeatures
