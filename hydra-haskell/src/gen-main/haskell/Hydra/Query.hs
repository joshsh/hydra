-- | A model for language-agnostic graph pattern queries

module Hydra.Query where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | One of several comparison operators
data ComparisonConstraint = 
  ComparisonConstraintEqual  |
  ComparisonConstraintNotEqual  |
  ComparisonConstraintLessThan  |
  ComparisonConstraintGreaterThan  |
  ComparisonConstraintLessThanOrEqual  |
  ComparisonConstraintGreaterThanOrEqual 
  deriving (Eq, Ord, Read, Show)

_ComparisonConstraint = (Core.Name "hydra/query.ComparisonConstraint")

_ComparisonConstraint_equal = (Core.Name "equal")

_ComparisonConstraint_notEqual = (Core.Name "notEqual")

_ComparisonConstraint_lessThan = (Core.Name "lessThan")

_ComparisonConstraint_greaterThan = (Core.Name "greaterThan")

_ComparisonConstraint_lessThanOrEqual = (Core.Name "lessThanOrEqual")

_ComparisonConstraint_greaterThanOrEqual = (Core.Name "greaterThanOrEqual")

-- | An abstract edge based on a record type
data Edge = 
  Edge {
    -- | The name of a record type, for which the edge also specifies an out- and an in- projection
    edgeType :: Core.Name,
    -- | The field representing the out-projection of the edge. Defaults to 'out'.
    edgeOut :: (Maybe Core.Name),
    -- | The field representing the in-projection of the edge. Defaults to 'in'.
    edgeIn :: (Maybe Core.Name)}
  deriving (Eq, Ord, Read, Show)

_Edge = (Core.Name "hydra/query.Edge")

_Edge_type = (Core.Name "type")

_Edge_out = (Core.Name "out")

_Edge_in = (Core.Name "in")

-- | A query pattern which matches within a designated component subgraph
data GraphPattern = 
  GraphPattern {
    -- | The name of the component graph
    graphPatternGraph :: Core.Name,
    -- | The patterns to match within the subgraph
    graphPatternPatterns :: [Pattern]}
  deriving (Eq, Ord, Read, Show)

_GraphPattern = (Core.Name "hydra/query.GraphPattern")

_GraphPattern_graph = (Core.Name "graph")

_GraphPattern_patterns = (Core.Name "patterns")

-- | A node in a query expression; it may be a term, a variable, or a wildcard
data Node = 
  -- | A graph term; an expression which is valid in the graph being matched
  NodeTerm Core.Term |
  -- | A query variable, not to be confused with a variable term
  NodeVariable Variable |
  -- | An anonymous variable which we do not care to join across patterns
  NodeWildcard 
  deriving (Eq, Ord, Read, Show)

_Node = (Core.Name "hydra/query.Node")

_Node_term = (Core.Name "term")

_Node_variable = (Core.Name "variable")

_Node_wildcard = (Core.Name "wildcard")

-- | A query path
data Path = 
  -- | A path given by a single step
  PathStep Step |
  -- | A path given by a regular expression quantifier applied to another path
  PathRegex RegexSequence |
  -- | A path given by the inverse of another path
  PathInverse Path
  deriving (Eq, Ord, Read, Show)

_Path = (Core.Name "hydra/query.Path")

_Path_step = (Core.Name "step")

_Path_regex = (Core.Name "regex")

_Path_inverse = (Core.Name "inverse")

-- | A query pattern
data Pattern = 
  -- | A subject/predicate/object pattern
  PatternTriple TriplePattern |
  -- | The negation of another pattern
  PatternNegation Pattern |
  -- | The conjunction ('and') of several other patterns
  PatternConjunction [Pattern] |
  -- | The disjunction (inclusive 'or') of several other patterns
  PatternDisjunction [Pattern] |
  -- | A pattern which matches within a named subgraph
  PatternGraph GraphPattern
  deriving (Eq, Ord, Read, Show)

_Pattern = (Core.Name "hydra/query.Pattern")

_Pattern_triple = (Core.Name "triple")

_Pattern_negation = (Core.Name "negation")

_Pattern_conjunction = (Core.Name "conjunction")

_Pattern_disjunction = (Core.Name "disjunction")

_Pattern_graph = (Core.Name "graph")

-- | A SELECT-style graph pattern matching query
data Query = 
  Query {
    -- | The variables selected by the query
    queryVariables :: [Variable],
    -- | The patterns to be matched
    queryPatterns :: [Pattern]}
  deriving (Eq, Ord, Read, Show)

_Query = (Core.Name "hydra/query.Query")

_Query_variables = (Core.Name "variables")

_Query_patterns = (Core.Name "patterns")

-- | A range from min to max, inclusive
data Range = 
  Range {
    rangeMin :: Int,
    rangeMax :: Int}
  deriving (Eq, Ord, Read, Show)

_Range = (Core.Name "hydra/query.Range")

_Range_min = (Core.Name "min")

_Range_max = (Core.Name "max")

-- | A regular expression quantifier
data RegexQuantifier = 
  -- | No quantifier; matches a single occurrence
  RegexQuantifierOne  |
  -- | The ? quanifier; matches zero or one occurrence
  RegexQuantifierZeroOrOne  |
  -- | The * quantifier; matches any number of occurrences
  RegexQuantifierZeroOrMore  |
  -- | The + quantifier; matches one or more occurrences
  RegexQuantifierOneOrMore  |
  -- | The {n} quantifier; matches exactly n occurrences
  RegexQuantifierExactly Int |
  -- | The {n,} quantifier; matches at least n occurrences
  RegexQuantifierAtLeast Int |
  -- | The {n, m} quantifier; matches between n and m (inclusive) occurrences
  RegexQuantifierRange Range
  deriving (Eq, Ord, Read, Show)

_RegexQuantifier = (Core.Name "hydra/query.RegexQuantifier")

_RegexQuantifier_one = (Core.Name "one")

_RegexQuantifier_zeroOrOne = (Core.Name "zeroOrOne")

_RegexQuantifier_zeroOrMore = (Core.Name "zeroOrMore")

_RegexQuantifier_oneOrMore = (Core.Name "oneOrMore")

_RegexQuantifier_exactly = (Core.Name "exactly")

_RegexQuantifier_atLeast = (Core.Name "atLeast")

_RegexQuantifier_range = (Core.Name "range")

-- | A path with a regex quantifier
data RegexSequence = 
  RegexSequence {
    regexSequencePath :: Path,
    regexSequenceQuantifier :: RegexQuantifier}
  deriving (Eq, Ord, Read, Show)

_RegexSequence = (Core.Name "hydra/query.RegexSequence")

_RegexSequence_path = (Core.Name "path")

_RegexSequence_quantifier = (Core.Name "quantifier")

-- | An atomic function as part of a query. When applied to a graph, steps are typed by function types.
data Step = 
  -- | An out-to-in traversal of an abstract edge
  StepEdge Edge |
  -- | A projection from a record through one of its fields
  StepProject Core.Projection |
  -- | A comparison of two terms
  StepCompare ComparisonConstraint
  deriving (Eq, Ord, Read, Show)

_Step = (Core.Name "hydra/query.Step")

_Step_edge = (Core.Name "edge")

_Step_project = (Core.Name "project")

_Step_compare = (Core.Name "compare")

-- | A subject/predicate/object pattern
data TriplePattern = 
  TriplePattern {
    triplePatternSubject :: Node,
    triplePatternPredicate :: Path,
    triplePatternObject :: Node}
  deriving (Eq, Ord, Read, Show)

_TriplePattern = (Core.Name "hydra/query.TriplePattern")

_TriplePattern_subject = (Core.Name "subject")

_TriplePattern_predicate = (Core.Name "predicate")

_TriplePattern_object = (Core.Name "object")

-- | A query variable
newtype Variable = 
  Variable {
    -- | A query variable
    unVariable :: String}
  deriving (Eq, Ord, Read, Show)

_Variable = (Core.Name "hydra/query.Variable")
