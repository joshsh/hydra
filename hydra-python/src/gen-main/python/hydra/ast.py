"""A model which provides a common syntax tree for Hydra serializers."""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum
from hydra.dsl.python import Node

class Associativity(Enum):
    """Operator associativity."""
    
    NONE = "none"
    
    LEFT = "left"
    
    RIGHT = "right"
    
    BOTH = "both"

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

class ExprConst(Node["Symbol"]): ...

class ExprIndent(Node["IndentedExpression"]): ...

class ExprOp(Node["OpExpr"]): ...

class ExprBrackets(Node["BracketExpr"]): ...

# An abstract expression.
type Expr = ExprConst | ExprIndent | ExprOp | ExprBrackets

@dataclass
class IndentedExpression:
    """An expression indented in a certain style."""
    
    style: IndentStyle
    expr: Expr

class IndentStyleAllLines(Node[str]): ...

class IndentStyleSubsequentLines(Node[str]): ...

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

class Precedence(Node[int]):
    """Operator precedence."""

class Symbol(Node[str]):
    """Any symbol."""

class WsNone(Node[None]): ...

class WsSpace(Node[None]): ...

class WsBreak(Node[None]): ...

class WsBreakAndIndent(Node[str]): ...

class WsDoubleBreak(Node[None]): ...

# One of several classes of whitespace.
type Ws = WsNone | WsSpace | WsBreak | WsBreakAndIndent | WsDoubleBreak