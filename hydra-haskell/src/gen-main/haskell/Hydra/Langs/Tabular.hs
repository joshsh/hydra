-- | A simple, untyped tabular data model, suitable for CSVs and TSVs

module Hydra.Langs.Tabular where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | A data row, containing untyped cells; one per column
newtype DataRow = 
  DataRow {
    -- | A data row, containing untyped cells; one per column
    unDataRow :: [String]}
  deriving (Eq, Ord, Read, Show)

_DataRow = (Core.Name "hydra/langs/tabular.DataRow")

-- | A header row, containing column names (but no types or data)
newtype HeaderRow = 
  HeaderRow {
    -- | A header row, containing column names (but no types or data)
    unHeaderRow :: [String]}
  deriving (Eq, Ord, Read, Show)

_HeaderRow = (Core.Name "hydra/langs/tabular.HeaderRow")

-- | A simple table as in a CSV file, having an optional header row and any number of data rows
data Table = 
  Table {
    -- | The optional header row of the table. If present, the header must have the same number of cells as each data row.
    tableHeader :: (Maybe HeaderRow),
    -- | The data rows of the table. Each row must have the same number of cells.
    tableData :: [DataRow]}
  deriving (Eq, Ord, Read, Show)

_Table = (Core.Name "hydra/langs/tabular.Table")

_Table_header = (Core.Name "header")

_Table_data = (Core.Name "data")
