"""A common API for BNF-based grammars, specifying context-free languages"""

from __future__ import annotations
from typing import Annotated, Literal, NewType
from dataclasses import dataclass

Constant = Annotated[str, "A constant pattern"]

Grammar = Annotated[list[Production], "An enhanced Backus-Naur form (BNF) grammar"]

Label = Annotated[str, "A name for a pattern"]


@dataclass
class LabeledPattern:
    """A pattern together with a name (label)"""

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

Pattern = Annotated[
    PatternNil
    | PatternIgnored
    | PatternLabeled
    | PatternConstant
    | PatternRegex
    | PatternNonterminal
    | PatternSequence
    | PatternAlternatives
    | PatternOption
    | PatternStar
    | PatternPlus,
    "A pattern which matches valid expressions in the language",
]


@dataclass
class Production:
    """A BNF production"""

    symbol: Symbol

    pattern: Pattern


Regex = Annotated[str, "A regular expression"]

Symbol = Annotated[str, "A nonterminal symbol"]
