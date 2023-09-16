{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier0.Constraints where

-- Standard Tier-0 imports
import qualified Data.List             as L
import qualified Data.Map              as M
import qualified Data.Set              as S
import qualified Data.Maybe            as Y
import           Hydra.Dsl.Annotations
import           Hydra.Dsl.Bootstrap
import qualified Hydra.Dsl.Terms       as Terms
import           Hydra.Dsl.Types       as Types
import           Hydra.Sources.Core

import Hydra.Sources.Tier0.Query


hydraConstraintsModule :: Module
hydraConstraintsModule = Module ns elements [hydraCoreModule, hydraQueryModule] $
    Just "A model for path- and pattern-based graph constraints, which may be considered as part of the schema of a graph"
  where
    ns = Namespace "hydra/constraints"
    core = typeref $ moduleNamespace hydraCoreModule
    query = typeref $ moduleNamespace hydraQueryModule
    constraints = typeref ns
    def = datatype ns

    elements = [
      
      def "PathEquation" $
        doc "A declared equivalence between two abstract paths in a graph" $
        record [
          "left">: query "Path",
          "right">: query "Path"],

      def "PatternImplication" $
        doc "A pattern which, if it matches in a given graph, implies that another pattern must also match. Query variables are shared between the two patterns." $
        lambda "a" $ record [
          "antecedent">: query "Pattern" @@ "a",
          "consequent">: query "Pattern" @@ "a"]]
