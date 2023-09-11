-- | A module for miscellaneous tier-3 functions and constants.

module Hydra.Tier3 where

import qualified Hydra.Compute as Compute
import qualified Hydra.Core as Core
import qualified Hydra.Lib.Io as Io
import qualified Hydra.Lib.Lists as Lists
import qualified Hydra.Lib.Logic as Logic
import qualified Hydra.Lib.Maps as Maps
import qualified Hydra.Lib.Strings as Strings
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | Summarize a trace as a string
traceSummary :: (Compute.Trace -> String)
traceSummary t =  
  let keyvalLines = (Logic.ifElse [] (Lists.cons "key/value pairs: " (Lists.map toLine (Maps.toList (Compute.traceOther t)))) (Maps.isEmpty (Compute.traceOther t))) 
      messageLines = (Lists.nub (Compute.traceMessages t))
      toLine = (\pair -> Strings.cat [
              Strings.cat [
                Strings.cat [
                  "\t",
                  (fst pair)],
                ": "],
              (Io.showTerm (snd pair))])
  in (Strings.intercalate "\n" (Lists.concat2 messageLines keyvalLines))