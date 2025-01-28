-- | A collection of tools for working with comma-separated values (CSVs).

module Hydra.Tools.Csv where

import Hydra.Kernel
import Hydra.Ext.Tabular
import qualified Hydra.Ext.RelationalModel as RM
import Hydra.Tools.Tabular

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as Y


-- Untyped tables --------------------------------------------------------------

-- | Encodes a single DataRow as a line of a CSV, and vice versa.
--   No support for optional cells; only empty strings. No attempt is made to check that rows are of a consistent width.
dataRowCsvCoder :: Coder s s (DataRow String) String
dataRowCsvCoder = Coder encode decode
  where
    encode (DataRow cells) = pure $ encodeCsvLine $ Y.catMaybes cells
    decode line = pure $ DataRow $ fmap Just $ decodeCsvLine line

tableCsvCoder :: Bool -> Coder s s (Table String) [String]
tableCsvCoder hasHeader = Coder encode decode
  where
    encode (Table mheader rows) = do
        hrows <- headerRows
        drows <- CM.mapM (coderEncode dataRowCsvCoder) rows
        return $ hrows ++ drows
      where
        headerRows = if hasHeader
          then case mheader of
            Just (HeaderRow names) -> pure [encodeCsvLine names]
            Nothing -> fail "missing header"
          else pure []
    decode rows = do
        (mheader, rest) <- if hasHeader
          then if L.null rows
            then fail "missing header"
            else pure (Just $ HeaderRow $ decodeCsvLine $ head rows, tail rows)
          else pure (Nothing, rows)
        drows <- CM.mapM (coderDecode dataRowCsvCoder) rest
        return $ Table mheader drows


-- Relational tables -----------------------------------------------------------

type DomainCoders t v s = M.Map t (Coder s s v String)

relationCsvCoder :: (Ord t, Show t) => DomainCoders t v s -> RM.RelationSchema t -> Bool -> Flow s (Coder s s (RM.Relation v) [String])
relationCsvCoder coderMap schema hasHeader = do
    coder <- rowCsvCoder coderMap schema
    return $ Coder (encode coder) (decode coder)
  where
    encode coder (RM.Relation rows) = do
        dataRows <- CM.mapM (coderEncode coder) rows
        return $ headerRows ++ dataRows
      where
        headerRows = if hasHeader
          then [encodeCsvLine (RM.unColumnName . RM.columnSchemaName <$> (RM.relationSchemaColumns schema))]
          else []
    decode coder inRows = do
        outRows <- CM.mapM (coderDecode coder) dataRows
        return $ RM.Relation outRows
      where
        dataRows = if hasHeader then L.tail inRows else inRows

-- | Encodes a single Row as a line of a CSV, and vice versa.
rowCsvCoder :: (Ord t, Show t) => DomainCoders t v s -> RM.RelationSchema t -> Flow s (Coder s s (RM.Row v) String)
rowCsvCoder coderMap schema = do
    coders <- CM.mapM findCoder (RM.columnSchemaDomain <$> RM.relationSchemaColumns schema)
    return $ Coder (encode coders) (decode coders)
  where
    encode coders (RM.Row cells) = encodeCsvLine <$> (encodeCells coders cells)
    decode coders line = RM.Row <$> (decodeCells coders $ decodeCsvLine line)
    findCoder typ = case M.lookup typ coderMap of
      Nothing -> fail $ "no coder for type: " ++ show typ
      Just c -> pure c
    encodeCells coders = CM.zipWithM coderEncode coders
    decodeCells coders = CM.zipWithM coderDecode coders

stringCoders :: DomainCoders () String s
stringCoders = M.singleton () $ Coder encode decode
  where
    encode s = pure s
    decode s = pure s

stringSchema :: Int -> RM.RelationSchema ()
stringSchema len = RM.RelationSchema (RM.RelationName $ "StringTable" ++ show len) (colSchema <$> [1..len]) [] []
  where
    colSchema i = RM.ColumnSchema (RM.ColumnName $ "Column" ++ show i) ()

-- Common functions ------------------------------------------------------------

decodeCsvCell :: String -> String
decodeCsvCell ('"':xs) = decodeCsvQuotes (init xs)  -- Remove surrounding quotes
decodeCsvCell cell = cell  -- If not quoted, return as is

decodeCsvLine :: String -> [String]
decodeCsvLine xs = fmap decodeCsvCell (splitCsvLine xs)

decodeCsvQuotes :: String -> String
decodeCsvQuotes [] = []
decodeCsvQuotes ('"':'"':ys) = '"' : decodeCsvQuotes ys  -- Handle escaped quotes
decodeCsvQuotes (y:ys) = y : decodeCsvQuotes ys

encodeCsvCell :: String -> String
encodeCsvCell cell
  | any (`elem` cell) [',', '\n', '"'] = '"' : escapeCsvQuotes cell ++ "\""
  | otherwise = cell

encodeCsvLine :: [String] -> String
encodeCsvLine = L.intercalate "," . fmap encodeCsvCell

escapeCsvQuotes :: String -> String
escapeCsvQuotes [] = []
escapeCsvQuotes (x:xs)
  | x == '"'  = '"' : '"' : escapeCsvQuotes xs
  | otherwise = x : escapeCsvQuotes xs

splitCsvLine :: String -> [String]
splitCsvLine [] = []
splitCsvLine ('"':xs) = ('"':quoted ++ "\"") : splitCsvLine next
  where
    (quoted, rest) = span (/= '"') xs
    afterQuote = drop 1 rest  -- Skip closing quote
    next = dropWhile (== ',') afterQuote  -- Skip comma
splitCsvLine xs = cell : splitCsvLine (drop 1 rest)  -- Skip comma
  where
    (cell, rest) = break (== ',') xs
