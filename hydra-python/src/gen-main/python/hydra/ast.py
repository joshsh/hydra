"""A model which provides a common syntax tree for Hydra serializers"""

from __future__ import annotations
from typing import NewType
from dataclasses import dataclass
from enum import StrEnum


# Any symbol
Symbol = NewType("Symbol", str)


# Operator precedence
Precedence = NewType("Precedence", int)


# Whitespace
class WsLiteralType(StrEnum):
    """A literal class of whitespace"""

    NONE = "none"
    SPACE = "space"
    BREAK = "break"
    DOUBLE_BREAK = "doubleBreak"


WsBreakAndIndent = NewType("WsBreakAndIndent", str)


# One of several classes of whitespace
type Ws = WsLiteralType | WsBreakAndIndent


# An abstract expression
ExprConst = NewType("ExprConst", Symbol)
ExprIndent = NewType("ExprIndent", IndentedExpression)
ExprOp = NewType("ExprOp", OpExpr)
ExprBrackets = NewType("ExprBrackets", BracketExpr)

type Expr = ExprConst | ExprIndent | ExprOp | ExprBrackets

# Indentation styles
IndentStyleAllLines = NewType("IndentStyleAllLines", str)
IndentStyleSubsequentLines = NewType("IndentStyleSubsequentLines", str)

type IndentStyle = IndentStyleAllLines | IndentStyleSubsequentLines


class Associativity(StrEnum):
    """Operator associativity"""

    NONE = "none"
    LEFT = "left"
    RIGHT = "right"
    BOTH = "both"


@dataclass
class BlockStyle:
    """Formatting option for code blocks"""

    indent: str | None
    newline_before_content: bool
    newline_after_content: bool


@dataclass
class BracketExpr:
    """An expression enclosed by brackets"""

    brackets: Brackets
    enclosed: Expr
    style: BlockStyle


@dataclass
class Brackets:
    """Matching open and close bracket symbols"""

    open: Symbol
    close: Symbol


@dataclass
class IndentedExpression:
    """An expression indented in a certain style"""

    style: IndentStyle
    expr: Expr


@dataclass
class Op:
    """An operator symbol"""

    symbol: Symbol
    padding: Padding
    precedence: Precedence
    associativity: Associativity


@dataclass
class OpExpr:
    """An operator expression"""

    op: Op
    lhs: Expr
    rhs: Expr


@dataclass
class Padding:
    """Left and right padding for an operator"""

    left: Ws
    right: Ws
