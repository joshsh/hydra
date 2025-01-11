"""A model which provides a common syntax tree for Hydra serializers"""

from __future__ import annotations
from typing import Annotated, Callable, Literal, NewType, TypeVar
from dataclasses import dataclass, field
import hydra.core

AssociativityNone = Literal['none']

AssociativityLeft = Literal['left']

AssociativityRight = Literal['right']

AssociativityBoth = Literal['both']

Associativity = Annotated[AssociativityNone | AssociativityLeft | AssociativityRight | AssociativityBoth, 'Operator associativity']

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

ExprConst = NewType('ExprConst', Symbol)

ExprIndent = NewType('ExprIndent', IndentedExpression)

ExprOp = NewType('ExprOp', OpExpr)

ExprBrackets = NewType('ExprBrackets', BracketExpr)

Expr = Annotated[ExprConst | ExprIndent | ExprOp | ExprBrackets, 'An abstract expression']

@dataclass
class IndentedExpression:
    """An expression indented in a certain style"""

    style: IndentStyle
    
    expr: Expr

IndentStyleAllLines = NewType('IndentStyleAllLines', str)

IndentStyleSubsequentLines = NewType('IndentStyleSubsequentLines', str)

IndentStyle = Annotated[IndentStyleAllLines | IndentStyleSubsequentLines, 'Any of several indentation styles']

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

Precedence = Annotated[int, 'Operator precedence']

Symbol = Annotated[str, 'Any symbol']

WsNone = Literal['none']

WsSpace = Literal['space']

WsBreak = Literal['break']

WsBreakAndIndent = NewType('WsBreakAndIndent', str)

WsDoubleBreak = Literal['doubleBreak']

Ws = Annotated[WsNone | WsSpace | WsBreak | WsBreakAndIndent | WsDoubleBreak, 'One of several classes of whitespace']