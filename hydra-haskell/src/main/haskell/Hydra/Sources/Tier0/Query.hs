{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier0.Query where

-- Standard Tier-0 imports
import qualified Data.List             as L
import qualified Data.Map              as M
import qualified Data.Set              as S
import qualified Data.Maybe            as Y
import           Hydra.Dsl.Annotations
import           Hydra.Dsl.Bootstrap
import qualified Hydra.Dsl.Terms       as Terms
import           Hydra.Dsl.Types       as Types
import           Hydra.Sources.Core


hydraQueryModule :: Module
hydraQueryModule = Module ns elements [hydraCoreModule] $
    Just "A model for language-agnostic graph pattern queries"
  where
    ns = Namespace "hydra/query"
    core = typeref $ moduleNamespace hydraCoreModule
    query = typeref ns
    def = datatype ns

    elements = [
      def "ComparisonConstraint" $
        doc "One of several comparison operators" $
        enum ["equal", "notEqual", "lessThan", "greaterThan", "lessThanOrEqual", "greaterThanOrEqual"],

      def "Edge" $
        doc "An abstract edge based on a record type" $
        record [
          "type">:
            doc "The name of a record type, for which the edge also specifies an out- and an in- projection" $
            core "Name",
          "out">:
            doc "The field representing the out-projection of the edge. Defaults to 'out'." $
            optional $ core "FieldName",
          "in">:
            doc "The field representing the in-projection of the edge. Defaults to 'in'." $
            optional $ core "FieldName"],

      def "GraphPattern" $
        doc "A query pattern which matches within a designated component subgraph" $
        lambda "a" $ record [
          "graph">:
            doc "The name of the component graph" $
            core "Name",
          "patterns">:
            doc "The patterns to match within the subgraph" $
            list (query "Pattern" @@ "a")],

      def "Node" $
        doc "A node in a query expression; it may be a term, a variable, or a wildcard" $
        lambda "a" $ union [
          "term">:
            doc "A graph term; an expression which is valid in the graph being matched" $
            core "Term" @@ "a",
          "variable">:
            doc "A query variable, not to be confused with a variable term" $
            query "Variable",
          "wildcard">:
            doc "An anonymous variable which we do not care to join across patterns" unit],

      def "Path" $
        doc "A query path" $
        union [
          "step">:
            doc "A path given by a single step" $
            query "Step",
          "regex">:
            doc "A path given by a regular expression quantifier applied to another path" $
            query "RegexSequence",
          "inverse">:
            doc "A path given by the inverse of another path" $
            query "Path"],

      def "Pattern" $
        doc "A query pattern" $
        lambda "a" $ union [
          "triple">:
            doc "A subject/predicate/object pattern" $
            query "TriplePattern" @@ "a",
          "negation">:
            doc "The negation of another pattern" $
            query "Pattern" @@ "a",
          "conjunction">:
            doc "The conjunction ('and') of several other patterns" $
            list (query "Pattern" @@ "a"),
          "disjunction">:
            doc "The disjunction (inclusive 'or') of several other patterns" $
            list (query "Pattern" @@ "a"),
          "graph">:
            doc "A pattern which matches within a named subgraph" $
            query "GraphPattern" @@ "a"],

      def "Query" $
        doc "A SELECT-style graph pattern matching query" $
        lambda "a" $ record [
          "variables">:
            doc "The variables selected by the query" $
            list $ query "Variable",
          "patterns">:
            doc "The patterns to be matched" $
            list (query "Pattern" @@ "a")],

      def "Range" $
        doc "A range from min to max, inclusive" $
        record [
          "min">: int32,
          "max">: int32],

      def "RegexQuantifier" $
        doc "A regular expression quantifier" $
        union [
          "one">: doc "No quantifier; matches a single occurrence" unit,
          "zeroOrOne">: doc "The ? quanifier; matches zero or one occurrence" unit,
          "zeroOrMore">: doc "The * quantifier; matches any number of occurrences" unit,
          "oneOrMore">: doc "The + quantifier; matches one or more occurrences" unit,
          "exactly">: doc "The {n} quantifier; matches exactly n occurrences" int32,
          "atLeast">: doc "The {n,} quantifier; matches at least n occurrences" int32,
          "range">: doc "The {n, m} quantifier; matches between n and m (inclusive) occurrences" $ query "Range"],

      def "RegexSequence" $
        doc "A path with a regex quantifier" $
        record [
          "path">: query "Path",
          "quantifier">: query "RegexQuantifier"],

      def "Step" $
        doc "An atomic function as part of a query. When applied to a graph, steps are typed by function types." $
        union [
          "edge">:
            doc "An out-to-in traversal of an abstract edge" $
            query "Edge",
          "project">:
            doc "A projection from a record through one of its fields" $
            core "Projection",
          "compare">:
            doc "A comparison of two terms" $
            query "ComparisonConstraint"],

      def "TriplePattern" $
        doc "A subject/predicate/object pattern" $
        lambda "a" $ record [
          "subject">: query "Node" @@ "a",
          "predicate">: query "Path",
          "object">: query "Node" @@ "a"],

      def "Variable" $
        doc "A query variable"
        string]
