{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier0.Testing where

-- Standard Tier-0 imports
import qualified Data.List             as L
import qualified Data.Map              as M
import qualified Data.Set              as S
import qualified Data.Maybe            as Y
import           Hydra.Dsl.Annotations
import           Hydra.Dsl.Bootstrap
import qualified Hydra.Dsl.Terms       as Terms
import           Hydra.Dsl.Types       as Types
import           Hydra.Kernel
import           Hydra.Sources.Core


hydraTestingModule :: Module
hydraTestingModule = Module ns elements [hydraCoreModule] $
    Just "A model for unit testing"
  where
    ns = Namespace "hydra/testing"
    def = datatype ns
    core = typeref $ moduleNamespace hydraCoreModule
    testing = typeref ns

    elements = [

      def "EvaluationStyle" $
        doc "One of two evaluation styles: eager or lazy" $
        enum ["eager", "lazy"],

      def "TestCase" $
        doc "A simple test case with an input and an expected output" $
        record [
          "description">: optional string,
          "evaluationStyle">: testing "EvaluationStyle",
          "input">: core "Term",
          "output">: core "Term"],

      def "TestGroup" $
        doc "A collection of test cases with a name and optional description" $
        record [
          "name">: string,
          "description">: optional string,
          "subgroups">: list (testing "TestGroup"),
          "cases">: list (testing "TestCase")]]
