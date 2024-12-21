-- | A collection of tools for working with comma-separated values (CSVs).
--   Note: no error handling yet; e.g.

module Hydra.Tools.Csv where

import Hydra.Kernel
import Hydra.Ext.Tabular
import Hydra.Tools.Tabular

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Maybe as Y


-- | Encodes a single DataRow as a line of a CSV, and vice versa.
--   No support for optional cells; only empty strings. No attempt is made to check that rows are of a consistent width.
dataRowCsvCoder :: Coder s1 s2 (DataRow String) String
dataRowCsvCoder = Coder encode decode
  where
    encode (DataRow cells) = pure $ encodeCsvLine $ Y.catMaybes cells
    decode line = pure $ DataRow $ fmap Just $ decodeCsvLine line

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

tableCsvCoder :: Bool -> Coder s1 s2 (Table String) [String]
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



-- TODO: temporary
tryCsvEncoding :: String -> String
tryCsvEncoding = decodeCsvCell . encodeCsvCell

-- TODO: temporary
tryCsvLineEncoding :: String -> String
tryCsvLineEncoding = encodeCsvLine . decodeCsvLine
