module Hydra.Dsl.Lib.Io where

import Hydra.Core
import Hydra.Phantoms
import Hydra.Sources.Libraries
import qualified Hydra.Dsl.Terms as Terms


showTerm :: Datum (Term -> String)
showTerm = Datum $ Terms.primitive _io_showTerm

showType :: Datum (Type Kv -> String)
showType = Datum $ Terms.primitive _io_showType
