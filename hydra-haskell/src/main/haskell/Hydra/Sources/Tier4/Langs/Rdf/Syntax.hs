module Hydra.Sources.Tier4.Langs.Rdf.Syntax where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Types as Types
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap


rdfSyntaxModule :: Module
rdfSyntaxModule = Module ns elements [] $
    Just "An RDF 1.1 syntax model"
  where
    ns = Namespace "hydra/langs/rdf/syntax"
    def = datatype ns
    rdf = typeref ns

    elements = [

      def "BlankNode" string,

      def "RdfsClass"
        $ doc "Stand-in for rdfs:Class" unit,

      def "Dataset" $ set $ rdf "Quad",

      def "Description" $
        doc "A graph of RDF statements together with a distinguished subject and/or object node" $
        record [
          "subject">: rdf "Node",
          "graph">: rdf "Graph"],

      def "Graph" $ set $ rdf "Triple",

      def "Iri" $
        doc "An Internationalized Resource Identifier"
        string,

      def "IriOrLiteral" $
        doc ("An IRI or a literal; " ++
             "this type is a convenience for downstream models like SHACL which may exclude blank nodes") $
        union [
          "iri">: rdf "Iri",
          "literal">: rdf "Literal"],

      def "LangStrings" $
        doc "A convenience type which provides at most one string value per language, and optionally a value without a language" $
        Types.map (optional $ rdf "LanguageTag") string,

      def "LanguageTag" $
        doc "A BCP47 language tag"
        string,

      def "Literal" $
        doc "A value such as a string, number, or date" $
        record [
          "lexicalForm">:
            doc "a Unicode string, which should be in Normal Form C"
            string,
          "datatypeIri">:
            doc "an IRI identifying a datatype that determines how the lexical form maps to a literal value" $
            rdf "Iri",
          "languageTag">:
            doc "An optional language tag, present if and only if the datatype IRI is http://www.w3.org/1999/02/22-rdf-syntax-ns#langString" $
            optional $ rdf "LanguageTag"],

      def "Node" $
        union [
          "iri">: rdf "Iri",
          "bnode">: rdf "BlankNode",
          "literal">: rdf "Literal"],

      def "Property" $
        doc "A type representing an RDF property, and encapsulating its domain, range, and subclass relationships" $
        record [
          "domain">:
            doc "State that any resource that has a given property is an instance of one or more classes" $
            set $ rdf "RdfsClass",
          "range">:
            doc "States that the values of a property are instances of one or more classes" $
            set $ rdf "RdfsClass",
          "subPropertyOf">:
            set $ rdf "Property"],

      def "Quad" $
        doc "An RDF triple with an optional named graph component" $
        record [
          "subject">: rdf "Resource",
          "predicate">: rdf "Iri",
          "object">: rdf "Node",
          "graph">: optional $ rdf "Iri"],

      def "Resource" $
        union [
          "iri">: rdf "Iri",
          "bnode">: rdf "BlankNode"],

      def "Triple" $
        doc "An RDF triple defined by a subject, predicate, and object" $
        record [
          "subject">: rdf "Resource",
          "predicate">: rdf "Iri",
          "object">: rdf "Node"]]
