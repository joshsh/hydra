-- | A loose collection of tools for working with tabular data, including CSVs.

module Hydra.Tools.Tabular (
  referenceCoder,
  tabularAdapter,
) where

import Hydra.Kernel
import Hydra.Ext.Tabular
import Hydra.Lib.Io

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M


-- | Consumes a map of field names to value coders, producing a record coder.
--   The record coder maps records with concrete values on the left, to records with references on the right, and vice versa.
--   Fields not designated in the map are unaffected; they are simply copied as-is in either direction.
--   For fields designated in the map, terms on the right *must* be variables.
referenceCoder :: (M.Map Name (Coder s1 s2 Term Name)) -> Coder s1 s2 Record Record
referenceCoder fieldCoders = Coder encode decode
  where
    encode (Record tname fields) = Record tname <$> CM.sequence (encodeField <$> fields)
      where
        encodeField field@(Field fname fterm) = case M.lookup fname fieldCoders of
          Just coder -> Field fname <$> (TermVariable <$> coderEncode coder fterm)
          Nothing -> return field
    decode (Record tname fields) = Record tname <$> CM.sequence (decodeField <$> fields)
      where
        decodeField field@(Field fname fterm) = case M.lookup fname fieldCoders of
          Just coder -> case fterm of
            TermVariable v -> Field fname <$> coderDecode coder v
            _ -> unexpected "variable" (showTerm fterm)
          Nothing -> return field

-- | Consumes a row type and a cell-level coder, producing a record coder.
--   The record coder maps data rows on the left to records on the right, and vice versa.
tabularAdapter :: RowType -> (Type -> Coder s1 s2 (Maybe v) Term) -> Coder s1 s2 (DataRow v) Record
tabularAdapter (RowType typeName fieldTypes) cellAdapter = Coder encode decode
  where
    cellCoders = cellAdapter <$> (fieldTypeType <$> fieldTypes)
    encode (DataRow cells) = do
      values <- CM.zipWithM coderEncode cellCoders cells
      let fields = L.zipWith Field (fieldTypeName <$> fieldTypes) values
      return $ Record typeName fields
    decode (Record tname fields) = do
      if (tname /= typeName)
        then unexpected ("record of type " ++ unName typeName) ("record of type " ++ unName tname)
        else DataRow <$> CM.sequence (fieldDecoders <*> fields)
    fieldDecoders = L.zipWith decodeField fieldTypes cellCoders
      where
        decodeField fieldType coder field = if (fieldName field /= fieldTypeName fieldType)
          then unexpected ("field " ++ unName (fieldTypeName fieldType)) ("field " ++ unName (fieldName field))
          else coderDecode coder (fieldTerm field)
