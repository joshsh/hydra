module Hydra.Langs.Json.Coder (jsonCoder, jsonEncodeTerm, literalJsonCoder) where

import Hydra.Core
import Hydra.Compute
import Hydra.Graph
import Hydra.Strip
import Hydra.Basics
import Hydra.Tier1
import Hydra.Tier2
import Hydra.Adapters
import Hydra.TermAdapters
import Hydra.Langs.Json.Language
import Hydra.Lib.Literals
import Hydra.AdapterUtils
import qualified Hydra.Json as Json
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Control.Monad as CM
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


jsonCoder :: Type -> Flow Graph (Coder Graph Graph Term Json.Value)
jsonCoder typ = do
  adapter <- languageAdapter jsonLanguage typ
  coder <- jsonTermCoder $ adapterTarget adapter
  return $ composeCoders (adapterCoder adapter) coder

literalJsonCoder :: LiteralType -> Flow Graph (Coder Graph Graph Literal Json.Value)
literalJsonCoder at = pure $ case at of
  LiteralTypeBoolean -> Coder {
    coderEncode = \(LiteralBoolean b) -> pure $ Json.ValueBoolean b,
    coderDecode = \s -> case s of
      Json.ValueBoolean b -> pure $ LiteralBoolean b
      _ -> unexpected "boolean" $ show s}
  LiteralTypeFloat _ -> Coder {
    coderEncode = \(LiteralFloat (FloatValueBigfloat f)) -> pure $ Json.ValueNumber f,
    coderDecode = \s -> case s of
      Json.ValueNumber f -> pure $ LiteralFloat $ FloatValueBigfloat f
      _ -> unexpected "number" $ show s}
  LiteralTypeInteger _ -> Coder {
    coderEncode = \(LiteralInteger (IntegerValueBigint i)) -> pure $ Json.ValueNumber $ bigintToBigfloat i,
    coderDecode = \s -> case s of
      Json.ValueNumber f -> pure $ LiteralInteger $ IntegerValueBigint $ bigfloatToBigint f
      _ -> unexpected "number" $ show s}
  LiteralTypeString -> Coder {
    coderEncode = \(LiteralString s) -> pure $ Json.ValueString s,
    coderDecode = \s -> case s of
      Json.ValueString s' -> pure $ LiteralString s'
      _ -> unexpected "string" $ show s}

recordCoder :: RowType -> Flow Graph (Coder Graph Graph Term Json.Value)
recordCoder rt = do
    coders <- CM.mapM (\f -> (,) <$> pure f <*> jsonTermCoder (fieldTypeType f)) (rowTypeFields rt)
    return $ Coder (encode coders) (decode coders)
  where
    encode coders term = case stripTerm term of
      TermRecord (Record _ fields) -> Json.ValueObject . M.fromList . Y.catMaybes <$> CM.zipWithM encodeField coders fields
        where
          encodeField (ft, coder) (Field fname fv) = case (fieldTypeType ft, fv) of
            (TypeOptional _, TermOptional Nothing) -> pure Nothing
            _ -> Just <$> ((,) <$> pure (unName fname) <*> coderEncode coder fv)
      _ -> unexpected "record" $ show term
    decode coders n = case n of
      Json.ValueObject m -> Terms.record (rowTypeTypeName rt) <$> CM.mapM (decodeField m) coders -- Note: unknown fields are ignored
        where
          decodeField a (FieldType fname _, coder) = do
            v <- coderDecode coder $ Y.fromMaybe Json.ValueNull $ M.lookup (unName fname) m
            return $ Field fname v
      _ -> unexpected "mapping" $ show n
    getCoder coders fname = Y.maybe error pure $ M.lookup fname coders
      where
        error = fail $ "no such field: " ++ fname

jsonTermCoder :: Type -> Flow Graph (Coder Graph Graph Term Json.Value)
jsonTermCoder typ = case stripType typ of
  TypeLiteral at -> do
    ac <- literalJsonCoder at
    return Coder {
      coderEncode = \(TermLiteral av) -> coderEncode ac av,
      coderDecode = \n -> case n of
        s -> Terms.literal <$> coderDecode ac s}
  TypeList lt -> do
    lc <- jsonTermCoder lt
    return Coder {
      coderEncode = \(TermList els) -> Json.ValueArray <$> CM.mapM (coderEncode lc) els,
      coderDecode = \n -> case n of
        Json.ValueArray nodes -> Terms.list <$> CM.mapM (coderDecode lc) nodes
        _ -> unexpected "sequence" $ show n}
  TypeOptional ot -> do
    oc <- jsonTermCoder ot
    return Coder {
      coderEncode = \t -> case t of
        TermOptional el -> Y.maybe (pure Json.ValueNull) (coderEncode oc) el
        _ -> unexpected "optional term" $ show t,
      coderDecode = \n -> case n of
        Json.ValueNull -> pure $ Terms.optional Nothing
        _ -> Terms.optional . Just <$> coderDecode oc n}
  TypeMap (MapType kt vt) -> do
      kc <- jsonTermCoder kt
      vc <- jsonTermCoder vt
      cx <- getState
      let encodeEntry (k, v) = (,) (toString cx k) <$> coderEncode vc v
      let decodeEntry (k, v) = (,) (fromString cx k) <$> coderDecode vc v
      return Coder {
        coderEncode = \(TermMap m) -> Json.ValueObject . M.fromList <$> CM.mapM encodeEntry (M.toList m),
        coderDecode = \n -> case n of
          Json.ValueObject m -> Terms.map . M.fromList <$> CM.mapM decodeEntry (M.toList m)
          _ -> unexpected "mapping" $ show n}
    where
      toString cx v = if isStringKey cx
        then case stripTerm v of
          TermLiteral (LiteralString s) -> s
        else show v
      fromString cx s = Terms.string $ if isStringKey cx then s else read s
      isStringKey cx = stripType kt == Types.string
  TypeRecord rt -> recordCoder rt
  TypeVariable name -> return $ Coder encode decode
    where
      encode term = pure $ Json.ValueString $ show term
      decode term = fail $ "type variable " ++ unName name ++ " does not support decoding"
  _ -> fail $ "unsupported type in JSON: " ++ show (typeVariant typ)

-- | A simplistic, unidirectional encoding for terms as JSON values.
--   Not type-aware or injective; best used for human consumption.
jsonEncodeTerm :: Term -> Flow s Json.Value
jsonEncodeTerm term = case term of
      TermAnnotated (Annotated subj ann) -> do
          subjJson <- jsonEncodeTerm subj
          pairs <- CM.mapM encodePair (M.toList ann)
          let annJson = Json.ValueObject $ M.fromList pairs
          return $ Json.ValueObject $ M.fromList [
                    ("subject", subjJson),
                    ("annotation", annJson)]
        where
          encodePair (k, v) = do
            vJson <- jsonEncodeTerm v
            return (k, vJson)
      TermApplication (Application lhs rhs) -> do
        lhsJson <- jsonEncodeTerm lhs
        rhsJson <- jsonEncodeTerm rhs
        return $ Json.ValueObject $ M.fromList [
                  ("lhs", lhsJson),
                  ("rhs", rhsJson)]
      TermFunction f -> case f of
        FunctionElimination e -> pure $ Json.ValueString $ "[elimination]" -- TODO
        FunctionLambda (Lambda v dom body) -> do
          bodyJson <- jsonEncodeTerm body
          return $ Json.ValueObject $ M.fromList [
                  ("parameter", Json.ValueString $ unName v),
                  ("body", bodyJson)]
        FunctionPrimitive name -> return $ Json.ValueString $ "!" ++ unName name
      TermLet (Let bindings env) -> do
        bindingsJson <- CM.mapM fieldToJson bindings
        envJson <- jsonEncodeTerm env
        return $ Json.ValueObject $ M.fromList [
                  ("bindings", Json.ValueObject $ M.fromList bindingsJson),
                  ("environment", envJson)]
        where
          fieldToJson (Field v b) = do
            bJson <- jsonEncodeTerm b
            return (unName v, bJson)
      TermList terms -> Json.ValueArray <$> (CM.mapM jsonEncodeTerm terms)
      TermLiteral lit -> pure $ case lit of
        LiteralBinary s -> Json.ValueString s
        LiteralBoolean b -> Json.ValueBoolean b
        LiteralFloat f -> Json.ValueNumber $ floatValueToBigfloat f
        LiteralInteger i -> Json.ValueNumber $ bigintToBigfloat $ integerValueToBigint i
        LiteralString s -> Json.ValueString s
      TermMap m -> do
          keyvals <- CM.mapM keyValToJson $ M.toList m
          return $ Json.ValueObject $ M.fromList keyvals
        where
          keyValToJson (k, v) = do
            vson <- jsonEncodeTerm v
            return (keyToString k, vson)
          keyToString k = case stripTerm k of
            TermLiteral (LiteralString s) -> s
            TermWrap (Nominal _ k2) -> keyToString k2
            _ -> show k
      TermOptional m -> case m of
        Nothing -> pure Json.ValueNull
        Just term1 -> jsonEncodeTerm term1
      TermProduct els -> jsonEncodeTerm $ TermList els
      TermRecord (Record _ fields) -> do
        keyvals <- CM.mapM fieldToKeyval fields
        return $ Json.ValueObject $ M.fromList $ Y.catMaybes keyvals
      TermSet els -> jsonEncodeTerm $ TermList $ S.toList els
      TermStream _ -> fail $ "cannot JSON-encode stream terms"
      TermSum (Sum index size term) -> do
        termJson <- jsonEncodeTerm term
        return $ Json.ValueObject $ M.fromList [
          ("index", Json.ValueNumber $ fromIntegral index),
          ("size", Json.ValueNumber $ fromIntegral size),
          ("term", termJson)]
      TermUnion (Injection _ field) -> do
        mkeyval <- fieldToKeyval field
        return $ Json.ValueObject $ M.fromList $ case mkeyval of
          Nothing -> []
          Just keyval -> [keyval]
      TermVariable name -> pure $ Json.ValueString $ "?" ++ unName name -- TODO
      TermWrap (Nominal _ body) -> jsonEncodeTerm body
  where
    fieldToKeyval f = do
        mjson <- forTerm $ fieldTerm f
        return $ case mjson of
          Nothing -> Nothing
          Just j -> Just (unName $ fieldName f, j)
      where
        forTerm t = case t of
          TermOptional mt -> case mt of
            Nothing -> pure Nothing
            Just t' -> forTerm t'
          t' -> Just <$> jsonEncodeTerm t'
