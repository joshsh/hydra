"""A common API for BNF-based grammars, specifying context-free languages."""

from __future__ import annotations
from dataclasses import dataclass
from typing import Literal, NewType

# A constant pattern.
Constant = str

# An enhanced Backus-Naur form (BNF) grammar.
Grammar = list[Production]

# A name for a pattern.
Label = str

@dataclass
class LabeledPattern:
    """A pattern together with a name (label)."""

    label: Label
    pattern: Pattern

PatternNil = Literal["nil"]

PatternIgnored = NewType("PatternIgnored", Pattern)

PatternLabeled = NewType("PatternLabeled", LabeledPattern)

PatternConstant = NewType("PatternConstant", Constant)

PatternRegex = NewType("PatternRegex", Regex)

PatternNonterminal = NewType("PatternNonterminal", Symbol)

PatternSequence = NewType("PatternSequence", list[Pattern])

PatternAlternatives = NewType("PatternAlternatives", list[Pattern])

PatternOption = NewType("PatternOption", Pattern)

PatternStar = NewType("PatternStar", Pattern)

PatternPlus = NewType("PatternPlus", Pattern)

# A pattern which matches valid expressions in the language.
Pattern = PatternNil | PatternIgnored | PatternLabeled | PatternConstant | PatternRegex | PatternNonterminal | PatternSequence | PatternAlternatives | PatternOption | PatternStar | PatternPlus

@dataclass
class Production:
    """A BNF production."""

    symbol: Symbol
    pattern: Pattern

# A regular expression.
Regex = str

# A nonterminal symbol.
Symbol = str