module Hydra.Langs.Yaml.Coder (yamlCoder) where

import Hydra.Kernel
import Hydra.TermAdapters
import Hydra.Langs.Yaml.Language
import Hydra.AdapterUtils
import qualified Hydra.Langs.Yaml.Model as YM
import qualified Hydra.Dsl.Terms as Terms

import qualified Control.Monad as CM
import qualified Data.Map as M
import qualified Data.Maybe as Y


literalCoder :: LiteralType -> Flow (Graph Kv) (Coder (Graph Kv) (Graph Kv) Literal YM.Scalar)
literalCoder at = pure $ case at of
  LiteralTypeBoolean -> Coder {
    coderEncode = \(LiteralBoolean b) -> pure $ YM.ScalarBool b,
    coderDecode = \s -> case s of
      YM.ScalarBool b -> pure $ LiteralBoolean b
      _ -> unexpected "boolean" $ show s}
  LiteralTypeFloat _ -> Coder {
    coderEncode = \(LiteralFloat (FloatValueBigfloat f)) -> pure $ YM.ScalarFloat f,
    coderDecode = \s -> case s of
      YM.ScalarFloat f -> pure $ LiteralFloat $ FloatValueBigfloat f
      _ -> unexpected "floating-point value" $ show s}
  LiteralTypeInteger _ -> Coder {
    coderEncode = \(LiteralInteger (IntegerValueBigint i)) -> pure $ YM.ScalarInt i,
    coderDecode = \s -> case s of
      YM.ScalarInt i -> pure $ LiteralInteger $ IntegerValueBigint i
      _ -> unexpected "integer" $ show s}
  LiteralTypeString -> Coder {
    coderEncode = \(LiteralString s) -> pure $ YM.ScalarStr s,
    coderDecode = \s -> case s of
      YM.ScalarStr s' -> pure $ LiteralString s'
      _ -> unexpected "string" $ show s}

recordCoder :: RowType Kv -> Flow (Graph Kv) (Coder (Graph Kv) (Graph Kv) (Term) YM.Node)
recordCoder rt = do
    coders <- CM.mapM (\f -> (,) <$> pure f <*> termCoder (fieldTypeType f)) (rowTypeFields rt)
    return $ Coder (encode coders) (decode coders)
  where
    encode coders term = case stripTerm term of
      TermRecord (Record _ fields) -> YM.NodeMapping . M.fromList . Y.catMaybes <$> CM.zipWithM encodeField coders fields
        where
          encodeField (ft, coder) (Field (FieldName fn) fv) = case (fieldTypeType ft, fv) of
            (TypeOptional _, TermOptional Nothing) -> pure Nothing
            _ -> Just <$> ((,) <$> pure (yamlString fn) <*> coderEncode coder fv)
      _ -> unexpected "record" $ show term
    decode coders n = case n of
      YM.NodeMapping m -> Terms.record (rowTypeTypeName rt) <$>
          CM.mapM (decodeField m) coders -- Note: unknown fields are ignored
        where
          decodeField a (FieldType fname@(FieldName fn) ft, coder) = do
            v <- coderDecode coder $ Y.fromMaybe yamlNull $ M.lookup (yamlString fn) m
            return $ Field fname v
      _ -> unexpected "mapping" $ show n
    getCoder coders fname = Y.maybe error pure $ M.lookup fname coders
      where
        error = fail $ "no such field: " ++ fname

termCoder :: Type Kv -> Flow (Graph Kv) (Coder (Graph Kv) (Graph Kv) (Term) YM.Node)
termCoder typ = case stripType typ of
  TypeLiteral at -> do
    ac <- literalCoder at
    return Coder {
      coderEncode = \t -> case t of
         TermLiteral av -> YM.NodeScalar <$> coderEncode ac av
         _ -> unexpected "literal" $ show t,
      coderDecode = \n -> case n of
        YM.NodeScalar s -> Terms.literal <$> coderDecode ac s
        _ -> unexpected "scalar node" $ show n}
  TypeList lt -> do
    lc <- termCoder lt
    return Coder {
      coderEncode = \t -> case t of
         TermList els -> YM.NodeSequence <$> CM.mapM (coderEncode lc) els
         _ -> unexpected "list" $ show t,
      coderDecode = \n -> case n of
        YM.NodeSequence nodes -> Terms.list <$> CM.mapM (coderDecode lc) nodes
        _ -> unexpected "sequence" $ show n}
  TypeOptional ot -> do
    oc <- termCoder ot
    return Coder {
      coderEncode = \t -> case t of
         TermOptional el -> Y.maybe (pure yamlNull) (coderEncode oc) el
         _ -> unexpected "optional" $ show t,
      coderDecode = \n -> case n of
        YM.NodeScalar YM.ScalarNull -> pure $ Terms.optional Nothing
        _ -> Terms.optional . Just <$> coderDecode oc n}
  TypeMap (MapType kt vt) -> do
    kc <- termCoder kt
    vc <- termCoder vt
    let encodeEntry (k, v) = (,) <$> coderEncode kc k <*> coderEncode vc v
    let decodeEntry (k, v) = (,) <$> coderDecode kc k <*> coderDecode vc v
    return Coder {
      coderEncode = \t -> case t of
        TermMap m -> YM.NodeMapping . M.fromList <$> CM.mapM encodeEntry (M.toList m)
        _ -> unexpected "term" $ show t,
      coderDecode = \n -> case n of
        YM.NodeMapping m -> Terms.map . M.fromList <$> CM.mapM decodeEntry (M.toList m)
        _ -> unexpected "mapping" $ show n}
  TypeRecord rt -> recordCoder rt

yamlCoder :: Type Kv -> Flow (Graph Kv) (Coder (Graph Kv) (Graph Kv) (Term) YM.Node)
yamlCoder typ = do
  adapter <- languageAdapter yamlLanguage typ
  coder <- termCoder $ adapterTarget adapter
  return $ composeCoders (adapterCoder adapter) coder

yamlNull :: YM.Node
yamlNull = YM.NodeScalar YM.ScalarNull

yamlString :: String -> YM.Node
yamlString = YM.NodeScalar . YM.ScalarStr
