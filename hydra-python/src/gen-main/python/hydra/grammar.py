"""A common API for BNF-based grammars, specifying context-free languages."""

from __future__ import annotations
from dataclasses import dataclass
from hydra.dsl.python import Node

class Constant(Node[str]):
    """A constant pattern."""

# An enhanced Backus-Naur form (BNF) grammar.
type Grammar = list[Production]

class Label(Node[str]):
    """A name for a pattern."""

@dataclass
class LabeledPattern:
    """A pattern together with a name (label)."""
    
    label: Label
    pattern: Pattern

class PatternNil(Node[None]): ...

class PatternIgnored(Node["Pattern"]): ...

class PatternLabeled(Node["LabeledPattern"]): ...

class PatternConstant(Node["Constant"]): ...

class PatternRegex(Node["Regex"]): ...

class PatternNonterminal(Node["Symbol"]): ...

class PatternSequence(Node["list[Pattern]"]): ...

class PatternAlternatives(Node["list[Pattern]"]): ...

class PatternOption(Node["Pattern"]): ...

class PatternStar(Node["Pattern"]): ...

class PatternPlus(Node["Pattern"]): ...

# A pattern which matches valid expressions in the language.
type Pattern = PatternNil | PatternIgnored | PatternLabeled | PatternConstant | PatternRegex | PatternNonterminal | PatternSequence | PatternAlternatives | PatternOption | PatternStar | PatternPlus

@dataclass
class Production:
    """A BNF production."""
    
    symbol: Symbol
    pattern: Pattern

class Regex(Node[str]):
    """A regular expression."""

class Symbol(Node[str]):
    """A nonterminal symbol."""