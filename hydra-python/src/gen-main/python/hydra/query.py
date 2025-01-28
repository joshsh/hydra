"""A model for language-agnostic graph pattern queries."""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum
from hydra.dsl.python import Variant
from typing import Annotated, NewType
import hydra.core

class ComparisonConstraint(Enum):
    """One of several comparison operators."""
    
    EQUAL = "equal"
    
    NOT_EQUAL = "notEqual"
    
    LESS_THAN = "lessThan"
    
    GREATER_THAN = "greaterThan"
    
    LESS_THAN_OR_EQUAL = "lessThanOrEqual"
    
    GREATER_THAN_OR_EQUAL = "greaterThanOrEqual"

@dataclass
class Edge:
    """An abstract edge based on a record type."""
    
    type: Annotated[hydra.core.Name, "The name of a record type, for which the edge also specifies an out- and an in- projection"]
    out: Annotated[hydra.core.Name | None, "The field representing the out-projection of the edge. Defaults to 'out'."]
    in_: Annotated[hydra.core.Name | None, "The field representing the in-projection of the edge. Defaults to 'in'."]

@dataclass
class GraphPattern:
    """A query pattern which matches within a designated component subgraph."""
    
    graph: Annotated[hydra.core.Name, "The name of the component graph"]
    patterns: Annotated[list[Pattern], "The patterns to match within the subgraph"]

class NodeTerm(Variant["hydra.core.Term"]):
    """A graph term; an expression which is valid in the graph being matched."""

class NodeVariable(Variant["Variable"]):
    """A query variable, not to be confused with a variable term."""

class NodeWildcard(Variant[None]):
    """An anonymous variable which we do not care to join across patterns."""

# A node in a query expression; it may be a term, a variable, or a wildcard.
type Node = NodeTerm | NodeVariable | NodeWildcard

class PathStep(Variant["Step"]):
    """A path given by a single step."""

class PathRegex(Variant["RegexSequence"]):
    """A path given by a regular expression quantifier applied to another path."""

class PathInverse(Variant["Path"]):
    """A path given by the inverse of another path."""

# A query path.
type Path = PathStep | PathRegex | PathInverse

class PatternTriple(Variant["TriplePattern"]):
    """A subject/predicate/object pattern."""

class PatternNegation(Variant["Pattern"]):
    """The negation of another pattern."""

class PatternConjunction(Variant["list[Pattern]"]):
    """The conjunction ('and') of several other patterns."""

class PatternDisjunction(Variant["list[Pattern]"]):
    """The disjunction (inclusive 'or') of several other patterns."""

class PatternGraph(Variant["GraphPattern"]):
    """A pattern which matches within a named subgraph."""

# A query pattern.
type Pattern = PatternTriple | PatternNegation | PatternConjunction | PatternDisjunction | PatternGraph

@dataclass
class Query:
    """A SELECT-style graph pattern matching query."""
    
    variables: Annotated[list[Variable], "The variables selected by the query"]
    patterns: Annotated[list[Pattern], "The patterns to be matched"]

@dataclass
class Range:
    """A range from min to max, inclusive."""
    
    min: int
    max: int

class RegexQuantifierOne(Variant[None]):
    """No quantifier; matches a single occurrence."""

class RegexQuantifierZeroOrOne(Variant[None]):
    """The ? quanifier; matches zero or one occurrence."""

class RegexQuantifierZeroOrMore(Variant[None]):
    """The * quantifier; matches any number of occurrences."""

class RegexQuantifierOneOrMore(Variant[None]):
    """The + quantifier; matches one or more occurrences."""

class RegexQuantifierExactly(Variant[int]):
    """The {n} quantifier; matches exactly n occurrences."""

class RegexQuantifierAtLeast(Variant[int]):
    """The {n,} quantifier; matches at least n occurrences."""

class RegexQuantifierRange(Variant["Range"]):
    """The {n, m} quantifier; matches between n and m (inclusive) occurrences."""

# A regular expression quantifier.
type RegexQuantifier = RegexQuantifierOne | RegexQuantifierZeroOrOne | RegexQuantifierZeroOrMore | RegexQuantifierOneOrMore | RegexQuantifierExactly | RegexQuantifierAtLeast | RegexQuantifierRange

@dataclass
class RegexSequence:
    """A path with a regex quantifier."""
    
    path: Path
    quantifier: RegexQuantifier

class StepEdge(Variant["Edge"]):
    """An out-to-in traversal of an abstract edge."""

class StepProject(Variant["hydra.core.Projection"]):
    """A projection from a record through one of its fields."""

class StepCompare(Variant["ComparisonConstraint"]):
    """A comparison of two terms."""

# An atomic function as part of a query. When applied to a graph, steps are typed by function types.
type Step = StepEdge | StepProject | StepCompare

@dataclass
class TriplePattern:
    """A subject/predicate/object pattern."""
    
    subject: Node
    predicate: Path
    object: Node

# A query variable.
Variable = NewType("Variable", str)