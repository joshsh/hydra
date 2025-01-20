"""A common API for BNF-based grammars, specifying context-free languages."""

from __future__ import annotations
from dataclasses import dataclass
from hydra.dsl.types import Variant

# A constant pattern.
type Constant = str

# An enhanced Backus-Naur form (BNF) grammar.
type Grammar = list[Production]

# A name for a pattern.
type Label = str

@dataclass
class LabeledPattern:
    """A pattern together with a name (label)."""
    label: Label
    pattern: Pattern

class PatternNil(Variant[None]):
    pass

class PatternIgnored(Variant[Pattern]):
    pass

class PatternLabeled(Variant[LabeledPattern]):
    pass

class PatternConstant(Variant[Constant]):
    pass

class PatternRegex(Variant[Regex]):
    pass

class PatternNonterminal(Variant[Symbol]):
    pass

class PatternSequence(Variant[list[Pattern]]):
    pass

class PatternAlternatives(Variant[list[Pattern]]):
    pass

class PatternOption(Variant[Pattern]):
    pass

class PatternStar(Variant[Pattern]):
    pass

class PatternPlus(Variant[Pattern]):
    pass

# A pattern which matches valid expressions in the language.
type Pattern = PatternNil | PatternIgnored | PatternLabeled | PatternConstant | PatternRegex | PatternNonterminal | PatternSequence | PatternAlternatives | PatternOption | PatternStar | PatternPlus

@dataclass
class Production:
    """A BNF production."""
    symbol: Symbol
    pattern: Pattern

# A regular expression.
type Regex = str

# A nonterminal symbol.
type Symbol = str