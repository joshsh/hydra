-- | A common API for BNF-based grammars, specifying context-free languages

module Hydra.Grammar where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | A constant pattern
newtype Constant = 
  Constant {
    -- | A constant pattern
    unConstant :: String}
  deriving (Eq, Ord, Read, Show)

_Constant = (Core.Name "hydra/grammar.Constant")

-- | An enhanced Backus-Naur form (BNF) grammar
newtype Grammar = 
  Grammar {
    -- | An enhanced Backus-Naur form (BNF) grammar
    unGrammar :: [Production]}
  deriving (Eq, Ord, Read, Show)

_Grammar = (Core.Name "hydra/grammar.Grammar")

-- | A name for a pattern
newtype Label = 
  Label {
    -- | A name for a pattern
    unLabel :: String}
  deriving (Eq, Ord, Read, Show)

_Label = (Core.Name "hydra/grammar.Label")

-- | A pattern together with a name (label)
data LabeledPattern = 
  LabeledPattern {
    labeledPatternLabel :: Label,
    labeledPatternPattern :: Pattern}
  deriving (Eq, Ord, Read, Show)

_LabeledPattern = (Core.Name "hydra/grammar.LabeledPattern")

_LabeledPattern_label = (Core.FieldName "label")

_LabeledPattern_pattern = (Core.FieldName "pattern")

-- | A pattern which matches valid expressions in the language
data Pattern = 
  PatternNil  |
  PatternIgnored Pattern |
  PatternLabeled LabeledPattern |
  PatternConstant Constant |
  PatternRegex Regex |
  PatternNonterminal Symbol |
  PatternSequence [Pattern] |
  PatternAlternatives [Pattern] |
  PatternOption Pattern |
  PatternStar Pattern |
  PatternPlus Pattern
  deriving (Eq, Ord, Read, Show)

_Pattern = (Core.Name "hydra/grammar.Pattern")

_Pattern_nil = (Core.FieldName "nil")

_Pattern_ignored = (Core.FieldName "ignored")

_Pattern_labeled = (Core.FieldName "labeled")

_Pattern_constant = (Core.FieldName "constant")

_Pattern_regex = (Core.FieldName "regex")

_Pattern_nonterminal = (Core.FieldName "nonterminal")

_Pattern_sequence = (Core.FieldName "sequence")

_Pattern_alternatives = (Core.FieldName "alternatives")

_Pattern_option = (Core.FieldName "option")

_Pattern_star = (Core.FieldName "star")

_Pattern_plus = (Core.FieldName "plus")

-- | A BNF production
data Production = 
  Production {
    productionSymbol :: Symbol,
    productionPattern :: Pattern}
  deriving (Eq, Ord, Read, Show)

_Production = (Core.Name "hydra/grammar.Production")

_Production_symbol = (Core.FieldName "symbol")

_Production_pattern = (Core.FieldName "pattern")

-- | A regular expression
newtype Regex = 
  Regex {
    -- | A regular expression
    unRegex :: String}
  deriving (Eq, Ord, Read, Show)

_Regex = (Core.Name "hydra/grammar.Regex")

-- | A nonterminal symbol
newtype Symbol = 
  Symbol {
    -- | A nonterminal symbol
    unSymbol :: String}
  deriving (Eq, Ord, Read, Show)

_Symbol = (Core.Name "hydra/grammar.Symbol")