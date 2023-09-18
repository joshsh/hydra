{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier3.Tier3 where

-- Standard Tier-3 imports
import           Prelude hiding ((++))
import qualified Data.List                 as L
import qualified Data.Map                  as M
import qualified Data.Set                  as S
import qualified Data.Maybe                as Y
import           Hydra.Dsl.Base            as Base
import qualified Hydra.Dsl.Core            as Core
import qualified Hydra.Dsl.Graph           as Graph
import qualified Hydra.Dsl.Lib.Equality    as Equality
import qualified Hydra.Dsl.Lib.Flows       as Flows
import qualified Hydra.Dsl.Lib.Io          as Io
import qualified Hydra.Dsl.Lib.Lists       as Lists
import qualified Hydra.Dsl.Lib.Literals    as Literals
import qualified Hydra.Dsl.Lib.Logic       as Logic
import qualified Hydra.Dsl.Lib.Maps        as Maps
import qualified Hydra.Dsl.Lib.Math        as Math
import qualified Hydra.Dsl.Lib.Optionals   as Optionals
import qualified Hydra.Dsl.Lib.Sets        as Sets
import           Hydra.Dsl.Lib.Strings     as Strings
import qualified Hydra.Dsl.Module          as Module
import qualified Hydra.Dsl.Terms           as Terms
import qualified Hydra.Dsl.Types           as Types
import           Hydra.Sources.Tier2.All


tier3Definition :: String -> Datum a -> Definition a
tier3Definition = definitionInModule hydraTier3Module

hydraTier3Module :: Module
hydraTier3Module = Module (Namespace "hydra/tier3") elements [hydraCoreModule] $
    Just ("A module for miscellaneous tier-3 functions and constants.")
  where
   elements = [
     el traceSummaryDef
     ]

traceSummaryDef :: Definition (Trace -> String)
traceSummaryDef = tier3Definition "traceSummary" $
  doc "Summarize a trace as a string" $
--  function traceT stringT $
  lambda "t" $ (
    (Strings.intercalate @@ "\n" @@ (Lists.concat2 @@ var "messageLines" @@ var "keyvalLines"))
      `with` [
        "messageLines">: (Lists.nub @@ (Flows.traceMessages @@ var "t")),
        "keyvalLines">: Logic.ifElse
          @@ (list [])
          @@ (Lists.cons @@ "key/value pairs: "
            @@ (Lists.map @@ (var "toLine") @@ (Maps.toList @@ (Flows.traceOther @@ var "t"))))
          @@ (Maps.isEmpty @@ (Flows.traceOther @@ var "t")),
        "toLine">:
          function (pairT stringT termT) stringT $
          lambda "pair" $ "\t" ++ (first @@ var "pair") ++ ": " ++ (Io.showTerm @@ (second @@ var "pair"))])
