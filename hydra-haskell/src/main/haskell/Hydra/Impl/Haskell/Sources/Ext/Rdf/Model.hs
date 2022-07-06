module Hydra.Impl.Haskell.Sources.Ext.Rdf.Model where

import Hydra.Impl.Haskell.Sources.Core

import Hydra.Core
import Hydra.Graph
import Hydra.Impl.Haskell.Dsl.Types as Types
import Hydra.Impl.Haskell.Dsl.Standard


rdfModelModule :: Module Meta
rdfModelModule = Module rdfModel []

rdfModelName :: GraphName
rdfModelName = GraphName "hydra/ext/rdf/model"

rdfModel :: Graph Meta
rdfModel = Graph rdfModelName elements (const True) hydraCoreName
  where
    def = datatype rdfModelName
    rdf = nominal . qualify rdfModelName . Name

    elements = [

      def "BlankNode" string,
      
      def "Iri" string,
      
      def "Literal" $
        record [
          field "lexicalForm" string,
          field "datatypeIri" $ rdf "Iri",
          field "language" $ optional string],

      def "Resource" $
        union [
          field "iri" $ rdf "Iri",
          field "bnode" $ rdf "BlankNode"],

      def "Node" $
        union [
          field "iri" $ rdf "Iri",
          field "bnode" $ rdf "BlankNode",
          field "literal" $ rdf "Literal"],

      def "Quad" $
        record [
          field "subject" $ rdf "Resource",
          field "predicate" $ rdf "Iri",
          field "object" $ rdf "Node",
          field "graph" $ optional $ rdf "Iri"],

      def "Dataset" $ list $ rdf "Quad"]
