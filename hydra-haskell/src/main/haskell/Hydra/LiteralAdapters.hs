-- | Adapter framework for literal types and terms

module Hydra.LiteralAdapters (
  literalAdapter,
  floatAdapter,
  integerAdapter,
) where

import Hydra.Printing
import Hydra.AdapterUtils
import Hydra.Basics
import Hydra.Coders
import Hydra.Compute
import Hydra.Core
import Hydra.Graph
import Hydra.Lexical
import Hydra.Mantle
import Hydra.Tier1
import Hydra.Tier2

import qualified Data.List as L
import qualified Data.Set as S


literalAdapter :: LiteralType -> Flow (AdapterContext Kv) (SymmetricAdapter s LiteralType Literal)
literalAdapter lt = do
    cx <- getState
    chooseAdapter (alts cx) (supported cx) describeLiteralType lt
  where
    supported cx = literalTypeIsSupported (constraints cx)
    constraints cx = languageConstraints $ adapterContextLanguage cx

    alts cx t = case t of
        LiteralTypeBinary -> pure $ fallbackAdapter t
        LiteralTypeBoolean -> pure $ if noIntegerVars
            then fallbackAdapter t
            else do
              adapter <- integerAdapter IntegerTypeUint8
              let step' = adapterCoder adapter
              let step = Coder encode decode
                    where
                      encode (LiteralBoolean bv) = LiteralInteger <$> coderEncode step' (toInt bv)
                        where
                          toInt bv = IntegerValueUint8 $ if bv then 1 else 0
                      decode (LiteralInteger iv) = LiteralBoolean <$> do
                        (IntegerValueUint8 v) <- coderDecode step' iv
                        return $ v == 1
              return $ Adapter False t (LiteralTypeInteger $ adapterTarget adapter) step
        LiteralTypeFloat ft -> pure $ if noFloatVars
          then fallbackAdapter t
          else do
            adapter <- floatAdapter ft
            let step = bidirectional
                  $ \dir l -> case l of
                    LiteralFloat fv -> LiteralFloat <$> encodeDecode dir (adapterCoder adapter) fv
                    _ -> unexpected "floating-point literal" (show l)
            return $ Adapter (adapterIsLossy adapter) t (LiteralTypeFloat $ adapterTarget adapter) step
        LiteralTypeInteger it -> pure $ if noIntegerVars
          then fallbackAdapter t
          else do
            adapter <- integerAdapter it
            let step = bidirectional
                  $ \dir (LiteralInteger iv) -> LiteralInteger
                    <$> encodeDecode dir (adapterCoder adapter) iv
            return $ Adapter (adapterIsLossy adapter) t (LiteralTypeInteger $ adapterTarget adapter) step
        LiteralTypeString -> pure $ fail "no substitute for the literal string type"
      where
        noFloatVars = not (S.member LiteralVariantFloat $ languageConstraintsLiteralVariants $ constraints cx)
          || S.null (languageConstraintsFloatTypes $ constraints cx)
        noIntegerVars = not (S.member LiteralVariantInteger $ languageConstraintsLiteralVariants $ constraints cx)
          || S.null (languageConstraintsIntegerTypes $ constraints cx)
        noStrings = not $ supported cx LiteralTypeString

        fallbackAdapter t = if noStrings
            then fail "cannot serialize unsupported type; strings are unsupported"
            else warn msg $ pure $ Adapter False t LiteralTypeString step
          where
            msg = disclaimer False (describeLiteralType t) (describeLiteralType LiteralTypeString)
            step = Coder encode decode
              where
                -- TODO: this format is tied to Haskell
                encode av = pure $ LiteralString $ case av of
                  LiteralBinary s -> s
                  LiteralBoolean b -> if b then "true" else "false"
                  _ -> show av
                decode (LiteralString s) = pure $ case t of
                  LiteralTypeBinary -> LiteralBinary s
                  LiteralTypeBoolean -> LiteralBoolean $ s == "true"
                  _ -> read s

comparePrecision :: Precision -> Precision -> Ordering
comparePrecision p1 p2 = if p1 == p2 then EQ else case (p1, p2) of
  (PrecisionArbitrary, _) -> GT
  (_, PrecisionArbitrary) -> LT
  (PrecisionBits b1, PrecisionBits b2) -> compare b1 b2

disclaimer :: Bool -> String -> String -> String
disclaimer lossy source target = "replace " ++ source ++ " with " ++ target
  ++ if lossy then " (lossy)" else ""

floatAdapter :: FloatType -> Flow (AdapterContext Kv) (SymmetricAdapter s FloatType FloatValue)
floatAdapter ft = do
    cx <- getState
    let supported = floatTypeIsSupported $ languageConstraints $ adapterContextLanguage cx
    chooseAdapter alts supported describeFloatType ft
  where
    alts t = makeAdapter t <$> case t of
        FloatTypeBigfloat -> [FloatTypeFloat64, FloatTypeFloat32]
        FloatTypeFloat32 -> [FloatTypeFloat64, FloatTypeBigfloat]
        FloatTypeFloat64 -> [FloatTypeBigfloat, FloatTypeFloat32]
      where
        makeAdapter source target = warn msg $ pure $ Adapter lossy source target step
          where
            lossy = comparePrecision (floatTypePrecision source) (floatTypePrecision target) == GT
            step = Coder (pure . convertFloatValue target) (pure . convertFloatValue source)
            msg = disclaimer lossy (describeFloatType source) (describeFloatType target)

integerAdapter :: IntegerType -> Flow (AdapterContext Kv) (SymmetricAdapter s IntegerType IntegerValue)
integerAdapter it = do
    cx <- getState
    let supported = integerTypeIsSupported $ languageConstraints $ adapterContextLanguage cx
    chooseAdapter alts supported describeIntegerType it
  where
    alts t = makeAdapter t <$> case t of
        IntegerTypeBigint -> L.reverse unsignedPref
        IntegerTypeInt8 -> signed 1
        IntegerTypeInt16 -> signed 2
        IntegerTypeInt32 -> signed 3
        IntegerTypeInt64 -> signed 4
        IntegerTypeUint8 -> unsigned 1
        IntegerTypeUint16 -> unsigned 2
        IntegerTypeUint32 -> unsigned 3
        IntegerTypeUint64 -> unsigned 4
      where
        signed i = L.drop (i*2) signedPref ++ [IntegerTypeBigint] ++ L.drop (8-(i*2)+1) signedNonPref
        unsigned i = L.drop (i*2) unsignedPref ++ [IntegerTypeBigint] ++ L.drop (8-(i*2)+1) unsignedNonPref
        signedPref = interleave signedOrdered unsignedOrdered
        unsignedPref = interleave unsignedOrdered signedOrdered
        signedNonPref = L.reverse unsignedPref
        unsignedNonPref = L.reverse signedPref

        interleave xs ys = L.concat (L.transpose [xs, ys])

        signedOrdered = L.filter
          (\v -> integerTypeIsSigned v && integerTypePrecision v /= PrecisionArbitrary) integerTypes
        unsignedOrdered = L.filter
          (\v -> not (integerTypeIsSigned v) && integerTypePrecision v /= PrecisionArbitrary) integerTypes

        makeAdapter source target = warn msg $ pure $ Adapter lossy source target step
          where
            lossy = comparePrecision (integerTypePrecision source) (integerTypePrecision target) /= LT
            step = Coder (pure . convertIntegerValue target) (pure . convertIntegerValue source)
            msg = disclaimer lossy (describeIntegerType source) (describeIntegerType target)

convertFloatValue :: FloatType -> FloatValue -> FloatValue
convertFloatValue target = encoder . decoder
  where
    decoder fv = case fv of
      FloatValueBigfloat d -> d
      FloatValueFloat32 f -> realToFrac f
      FloatValueFloat64 d -> d
    encoder d = case target of
      FloatTypeBigfloat -> FloatValueBigfloat d
      FloatTypeFloat32 -> FloatValueFloat32 $ realToFrac d
      FloatTypeFloat64 -> FloatValueFloat64 d

convertIntegerValue :: IntegerType -> IntegerValue -> IntegerValue
convertIntegerValue target = encoder . decoder
  where
    decoder iv = case iv of
      IntegerValueBigint v -> v
      IntegerValueInt8 v -> fromIntegral v
      IntegerValueInt16 v -> fromIntegral v
      IntegerValueInt32 v -> fromIntegral v
      IntegerValueInt64 v -> fromIntegral v
      IntegerValueUint8 v -> fromIntegral v
      IntegerValueUint16 v -> fromIntegral v
      IntegerValueUint32 v -> fromIntegral v
      IntegerValueUint64 v -> fromIntegral v
    encoder d = case target of
      IntegerTypeBigint -> IntegerValueBigint d
      IntegerTypeInt8 -> IntegerValueInt8 $ fromIntegral d
      IntegerTypeInt16 -> IntegerValueInt16 $ fromIntegral d
      IntegerTypeInt32 -> IntegerValueInt32 $ fromIntegral d
      IntegerTypeInt64 -> IntegerValueInt64 $ fromIntegral d
      IntegerTypeUint8 -> IntegerValueUint8 $ fromIntegral d
      IntegerTypeUint16 -> IntegerValueUint16 $ fromIntegral d
      IntegerTypeUint32 -> IntegerValueUint32 $ fromIntegral d
      IntegerTypeUint64 -> IntegerValueUint64 $ fromIntegral d
