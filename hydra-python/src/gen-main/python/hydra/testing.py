"""A model for unit testing"""

from __future__ import annotations
from typing import Annotated, Callable, Literal, NewType, TypeVar
from dataclasses import dataclass, field
import hydra.core

EvaluationStyleEager = Literal["eager"]

EvaluationStyleLazy = Literal["lazy"]

EvaluationStyle = Annotated[
    EvaluationStyleEager | EvaluationStyleLazy,
    "One of two evaluation styles: eager or lazy",
]


@dataclass
class TestCase:
    """A simple test case with an input and an expected output"""

    description: str | None

    evaluation_style: EvaluationStyle

    input: hydra.core.Term

    output: hydra.core.Term


@dataclass
class TestGroup:
    """A collection of test cases with a name and optional description"""

    name: str

    description: str | None

    subgroups: list[TestGroup]

    cases: list[TestCase]
