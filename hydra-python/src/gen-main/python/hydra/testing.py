"""A model for unit testing."""

from __future__ import annotations
from dataclasses import dataclass
from hydra.dsl.types import Variant
import hydra.core

class EvaluationStyleEager(Variant[None]):
    pass

class EvaluationStyleLazy(Variant[None]):
    pass

# One of two evaluation styles: eager or lazy.
type EvaluationStyle = EvaluationStyleEager | EvaluationStyleLazy

@dataclass
class TestCase:
    """A simple test case with an input and an expected output."""
    description: str | None
    evaluation_style: EvaluationStyle
    input: hydra.core.Term
    output: hydra.core.Term

@dataclass
class TestGroup:
    """A collection of test cases with a name and optional description."""
    name: str
    description: str | None
    subgroups: list[TestGroup]
    cases: list[TestCase]