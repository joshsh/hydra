"""A model for unit testing."""

from dataclasses import dataclass
from enum import Enum
import hydra.core

class EvaluationStyle(Enum):
    """One of two evaluation styles: eager or lazy."""
    
    EAGER = "eager"
    
    LAZY = "lazy"

@dataclass
class TestCase:
    """A simple test case with an input and an expected output."""
    
    description: str | None
    evaluation_style: "EvaluationStyle"
    input: hydra.core.Term
    output: hydra.core.Term

@dataclass
class TestGroup:
    """A collection of test cases with a name and optional description."""
    
    name: str
    description: str | None
    subgroups: list["TestGroup"]
    cases: list["TestCase"]