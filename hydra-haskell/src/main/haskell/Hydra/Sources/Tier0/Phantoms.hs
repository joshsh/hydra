{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier0.Phantoms where

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

import Hydra.Sources.Tier0.Compute


hydraPhantomsModule :: Module
hydraPhantomsModule = Module ns elements [hydraComputeModule] [hydraCoreModule] $
    Just "Phantom types for use with Hydra DSLs"
  where
    ns = Namespace "hydra/phantoms"
    core = typeref $ moduleNamespace hydraCoreModule
    phantoms = typeref ns
    def = datatype ns

    elements = [

      def "TCase" $
        doc "An association of a field name (as in a case statement) with a phantom type" $
        lambda "a" $ wrap $ core "Name",

      def "TElement" $
        doc "An association with a named term (element) with a phantom type" $
        lambda "a" $ record [
          "name">: core "Name",
          "term">: phantoms "TTerm" @@ "a"],

      def "TField" $
        doc "An association with a term-level field with a phantom type" $
        lambda "a" $ wrap $ core "Field",

      def "TTerm" $
        doc "An association of a term with a phantom type" $
        lambda "a" $ wrap $ core "Term"]
