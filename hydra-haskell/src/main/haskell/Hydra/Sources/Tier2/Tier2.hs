{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier2.Tier2 where

-- Standard Tier-2 imports
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
import           Hydra.Sources.Tier1.All


tier2Definition :: String -> Datum a -> Definition a
tier2Definition = definitionInModule hydraTier2Module

hydraTier2Module :: Module
hydraTier2Module = Module (Namespace "hydra/tier2") elements [hydraGraphModule, hydraMantleModule, hydraComputeModule, hydraStripModule] $
    Just ("A module for miscellaneous tier-2 functions and constants.")
  where
   elements = [
     el getStateDef,
     el getTermTypeDef,
     el putStateDef,
     el requireElementTypeDef,
     el requireTermTypeDef,
     el unexpectedDef]

getStateDef :: Definition (Flow s s)
getStateDef = tier2Definition "getState" $
  doc "Get the state of the current flow" $
  typed flowSS $
  wrap _Flow (lambda "s0" $ lambda "t0" $ (
    (lambda "v" $ lambda "s" $ lambda "t" $ (
      (matchOpt
        (Flows.flowState nothing (var "s") (var "t"))
        (constant (Flows.flowState (just $ var "s") (var "s") (var "t"))))
       @@ var "v"))
    @@ (Flows.flowStateValue @@ var "fs1") @@ (Flows.flowStateState @@ var "fs1") @@ (Flows.flowStateTrace @@ var "fs1"))
  `with` [
    "fs1">:
      typed (Types.apply (Types.apply (TypeVariable _FlowState) sT) unitT) $
      Flows.unFlow @@ (Flows.pure @@ unit) @@ var "s0" @@ var "t0"])

getTermTypeDef :: Definition (Term -> Flow Graph (Maybe Type))
getTermTypeDef = tier2Definition "getTermType" $
  function termT (flowT graphT (optionalT typeT)) $
  doc "Get the annotated type of a given term, if any" $
  lambda "term" ((Flows.bind @@ (Flows.map @@ (project _Graph _Graph_annotations) @@ ref getStateDef) @@ var "annsToType")
  `with` [
    "annsToType">: lambda "anns" $ (project _AnnotationClass _AnnotationClass_termType @@ var "anns" @@ var "term")])

putStateDef :: Definition (s -> Flow s ())
putStateDef = tier2Definition "putState" $
  doc "Set the state of a flow" $
  function sT (flowT sT unitT) $
  lambda "cx" $ wrap _Flow $ lambda "s0" $ lambda "t0" (
    (Flows.flowState
      (Flows.flowStateValue @@ var "f1")
      (var "cx")
      (Flows.flowStateTrace @@ var "f1"))
    `with` [
      "f1">: Flows.unFlow @@ (Flows.pure @@ unit) @@ var "s0" @@ var "t0"])

requireElementTypeDef :: Definition (Element -> Flow Graph Type)
requireElementTypeDef = tier2Definition "requireElementType" $
  function elementT (flowT graphT typeT) $
  doc "Get the annotated type of a given element, or fail if it is missing" $
  lambda "el" ((Flows.bind @@ (ref getTermTypeDef @@ (project _Element _Element_data @@ var "el")) @@ var "withType")
    `with` [
      "withType">: matchOpt
       (Flows.fail @@ ("missing type annotation for element " ++ (unwrap _Name @@ (project _Element _Element_name @@ var "el"))))
       Flows.pure])

requireTermTypeDef :: Definition (Term -> Flow Graph Type)
requireTermTypeDef = tier2Definition "requireTermType" $
  function termT (flowT graphT typeT) $
  doc "Get the annotated type of a given term, or fail if it is missing" $
  lambda "term" ((Flows.bind @@ (ref getTermTypeDef @@ var "term") @@ var "withType")
    `with` [
      "withType">: matchOpt
       (Flows.fail @@ "missing type annotation")
       Flows.pure])

unexpectedDef :: Definition (String -> String -> Flow s a)
unexpectedDef = tier2Definition "unexpected" $
  functionN [stringT, stringT, flowT sT aT] $
  doc "Fail if an actual value does not match an expected value" $
  lambda "expected" $ lambda "actual" $ Flows.fail @@ ("expected " ++ var "expected" ++ " but found: " ++ var "actual")
