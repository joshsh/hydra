-- | A model for Hydra labeled-BNF grammars

module Hydra.Sources.Tier0.Grammar where

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


hydraGrammarModule :: Module
hydraGrammarModule = Module ns elements [hydraCoreModule] $
    Just "A common API for BNF-based grammars, specifying context-free languages"
  where
    ns = Namespace "hydra/grammar"
    grammar = typeref ns
    def = datatype ns

    elements = [

      def "Constant" $
        doc "A constant pattern"
        string,

      def "Grammar" $
        doc "An enhanced Backus-Naur form (BNF) grammar" $
        list $ grammar "Production",

      def "Label" $
        doc "A name for a pattern"
        string,

      def "LabeledPattern" $
        doc "A pattern together with a name (label)" $
        record [
        "label">: grammar "Label",
        "pattern">: grammar "Pattern"],

      def "Pattern" $
        doc "A pattern which matches valid expressions in the language" $
        union [
          "nil">: unit,
          "ignored">: grammar "Pattern",
          "labeled">: grammar "LabeledPattern",
          "constant">: grammar "Constant",
          "regex">: grammar "Regex",
          "nonterminal">: grammar "Symbol",
          "sequence">: list $ grammar "Pattern",
          "alternatives">: list $ grammar "Pattern",
          "option">: grammar "Pattern",
          "star">: grammar "Pattern",
          "plus">: grammar "Pattern"],

      def "Production" $
        doc "A BNF production" $
        record [
          "symbol">: grammar "Symbol",
          "pattern">: grammar "Pattern"],

      def "Regex" $
        doc "A regular expression"
        string,

      def "Symbol" $
        doc "A nonterminal symbol"
        string]
