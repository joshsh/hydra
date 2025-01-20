"""A model for language-agnostic graph pattern queries."""

from __future__ import annotations
from dataclasses import dataclass
from typing import Annotated, Literal, NewType
import hydra.core

ComparisonConstraintEqual = Literal["equal"]

ComparisonConstraintNotEqual = Literal["notEqual"]

ComparisonConstraintLessThan = Literal["lessThan"]

ComparisonConstraintGreaterThan = Literal["greaterThan"]

ComparisonConstraintLessThanOrEqual = Literal["lessThanOrEqual"]

ComparisonConstraintGreaterThanOrEqual = Literal["greaterThanOrEqual"]

# One of several comparison operators.
ComparisonConstraint = ComparisonConstraintEqual | ComparisonConstraintNotEqual | ComparisonConstraintLessThan | ComparisonConstraintGreaterThan | ComparisonConstraintLessThanOrEqual | ComparisonConstraintGreaterThanOrEqual

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

# A graph term; an expression which is valid in the graph being matched
NodeTerm = NewType("NodeTerm", hydra.core.Term)

# A query variable, not to be confused with a variable term
NodeVariable = NewType("NodeVariable", Variable)

NodeWildcard = Literal["wildcard"]

# A node in a query expression; it may be a term, a variable, or a wildcard.
Node = NodeTerm | NodeVariable | NodeWildcard

# A path given by a single step
PathStep = NewType("PathStep", Step)

# A path given by a regular expression quantifier applied to another path
PathRegex = NewType("PathRegex", RegexSequence)

# A path given by the inverse of another path
PathInverse = NewType("PathInverse", Path)

# A query path.
Path = PathStep | PathRegex | PathInverse

# A subject/predicate/object pattern
PatternTriple = NewType("PatternTriple", TriplePattern)

# The negation of another pattern
PatternNegation = NewType("PatternNegation", Pattern)

# The conjunction ('and') of several other patterns
PatternConjunction = NewType("PatternConjunction", list[Pattern])

# The disjunction (inclusive 'or') of several other patterns
PatternDisjunction = NewType("PatternDisjunction", list[Pattern])

# A pattern which matches within a named subgraph
PatternGraph = NewType("PatternGraph", GraphPattern)

# A query pattern.
Pattern = PatternTriple | PatternNegation | PatternConjunction | PatternDisjunction | PatternGraph

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

RegexQuantifierOne = Literal["one"]

RegexQuantifierZeroOrOne = Literal["zeroOrOne"]

RegexQuantifierZeroOrMore = Literal["zeroOrMore"]

RegexQuantifierOneOrMore = Literal["oneOrMore"]

# The {n} quantifier; matches exactly n occurrences
RegexQuantifierExactly = NewType("RegexQuantifierExactly", int)

# The {n,} quantifier; matches at least n occurrences
RegexQuantifierAtLeast = NewType("RegexQuantifierAtLeast", int)

# The {n, m} quantifier; matches between n and m (inclusive) occurrences
RegexQuantifierRange = NewType("RegexQuantifierRange", Range)

# A regular expression quantifier.
RegexQuantifier = RegexQuantifierOne | RegexQuantifierZeroOrOne | RegexQuantifierZeroOrMore | RegexQuantifierOneOrMore | RegexQuantifierExactly | RegexQuantifierAtLeast | RegexQuantifierRange

@dataclass
class RegexSequence:
    """A path with a regex quantifier."""

    path: Path
    quantifier: RegexQuantifier

# An out-to-in traversal of an abstract edge
StepEdge = NewType("StepEdge", Edge)

# A projection from a record through one of its fields
StepProject = NewType("StepProject", hydra.core.Projection)

# A comparison of two terms
StepCompare = NewType("StepCompare", ComparisonConstraint)

# An atomic function as part of a query. When applied to a graph, steps are typed by function types.
Step = StepEdge | StepProject | StepCompare

@dataclass
class TriplePattern:
    """A subject/predicate/object pattern."""

    subject: Node
    predicate: Path
    object: Node

# A query variable.
Variable = str