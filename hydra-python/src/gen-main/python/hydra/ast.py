"""A model which provides a common syntax tree for Hydra serializers."""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum
from hydra.dsl.types import Variant

class Associativity(Enum):
    """Operator associativity."""
    
    ASSOCIATIVITY_NONE = "none"
    ASSOCIATIVITY_LEFT = "left"
    ASSOCIATIVITY_RIGHT = "right"
    ASSOCIATIVITY_BOTH = "both"

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

class ExprConst(Variant[Symbol]): ...

class ExprIndent(Variant[IndentedExpression]): ...

class ExprOp(Variant[OpExpr]): ...

class ExprBrackets(Variant[BracketExpr]): ...

# An abstract expression.
type Expr = ExprConst | ExprIndent | ExprOp | ExprBrackets

@dataclass
class IndentedExpression:
    """An expression indented in a certain style."""
    
    style: IndentStyle
    expr: Expr

class IndentStyleAllLines(Variant[str]): ...

class IndentStyleSubsequentLines(Variant[str]): ...

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

class WsNone(Variant[None]): ...

class WsSpace(Variant[None]): ...

class WsBreak(Variant[None]): ...

class WsBreakAndIndent(Variant[str]): ...

class WsDoubleBreak(Variant[None]): ...

# One of several classes of whitespace.
type Ws = WsNone | WsSpace | WsBreak | WsBreakAndIndent | WsDoubleBreak