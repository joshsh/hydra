"""A model which provides a common syntax tree for Hydra serializers."""

from __future__ import annotations
from dataclasses import dataclass
from hydra.dsl.types import Variant

class AssociativityNone(Variant[None]):
    pass

class AssociativityLeft(Variant[None]):
    pass

class AssociativityRight(Variant[None]):
    pass

class AssociativityBoth(Variant[None]):
    pass

# Operator associativity.
type Associativity = AssociativityNone | AssociativityLeft | AssociativityRight | AssociativityBoth

@dataclass
class BlockStyle:
    """Formatting option for code blocks."""
    indent: str | None
    newline_before_content: bool
    newline_after_content: bool

@dataclass
class BracketExpr:
    """An expression enclosed by brackets."""
    brackets: Brackets
    enclosed: Expr
    style: BlockStyle

@dataclass
class Brackets:
    """Matching open and close bracket symbols."""
    open: Symbol
    close: Symbol

class ExprConst(Variant[Symbol]):
    pass

class ExprIndent(Variant[IndentedExpression]):
    pass

class ExprOp(Variant[OpExpr]):
    pass

class ExprBrackets(Variant[BracketExpr]):
    pass

# An abstract expression.
type Expr = ExprConst | ExprIndent | ExprOp | ExprBrackets

@dataclass
class IndentedExpression:
    """An expression indented in a certain style."""
    style: IndentStyle
    expr: Expr

class IndentStyleAllLines(Variant[str]):
    pass

class IndentStyleSubsequentLines(Variant[str]):
    pass

# Any of several indentation styles.
type IndentStyle = IndentStyleAllLines | IndentStyleSubsequentLines

@dataclass
class Op:
    """An operator symbol."""
    symbol: Symbol
    padding: Padding
    precedence: Precedence
    associativity: Associativity

@dataclass
class OpExpr:
    """An operator expression."""
    op: Op
    lhs: Expr
    rhs: Expr

@dataclass
class Padding:
    """Left and right padding for an operator."""
    left: Ws
    right: Ws

# Operator precedence.
type Precedence = int

# Any symbol.
type Symbol = str

class WsNone(Variant[None]):
    pass

class WsSpace(Variant[None]):
    pass

class WsBreak(Variant[None]):
    pass

class WsBreakAndIndent(Variant[str]):
    pass

class WsDoubleBreak(Variant[None]):
    pass

# One of several classes of whitespace.
type Ws = WsNone | WsSpace | WsBreak | WsBreakAndIndent | WsDoubleBreak