{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Langs.Shacl.Model where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Sources.Tier4.Langs.Rdf.Syntax
import Hydra.Dsl.Types as Types


shaclModelModule :: Module
shaclModelModule = Module ns elements [rdfSyntaxModule] $
    Just "A SHACL syntax model. See https://www.w3.org/TR/shacl"
  where
    ns = Namespace "hydra/langs/shacl/model"
    def = datatype ns
    shacl = typeref ns
    rdf = typeref $ moduleNamespace rdfSyntaxModule

    elements = [

      def "Closed" $
        see "https://www.w3.org/TR/shacl/#ClosedPatterConstraintComponent" $
        record [
          "isClosed">: boolean,
          "ignoredProperties">: optional $ set $ rdf "Property"],

      def "CommonConstraint" $
        doc "Any of a number of constraint parameters which can be applied either to node or property shapes" $
        union [
          "and">:
            see "https://www.w3.org/TR/shacl/#AndConstraintComponent" $
            set $ shacl "Reference" @@ shacl "Shape",

          "closed">:
            see "https://www.w3.org/TR/shacl/#ClosedConstraintComponent" $
            shacl "Closed",

          "class">:
            see "https://www.w3.org/TR/shacl/#ClassConstraintComponent" $
            set $ rdf "RdfsClass",

          "datatype">:
            see "https://www.w3.org/TR/shacl/#DatatypeConstraintComponent" $
            rdf "Iri",

          "disjoint">:
            see "https://www.w3.org/TR/shacl/#DisjointConstraintComponent" $
            set $ rdf "Property",

          "equals">:
            see "https://www.w3.org/TR/shacl/#EqualsConstraintComponent" $
            set $ rdf "Property",

          "hasValue">:
            doc ("Specifies the condition that at least one value node is equal to the given RDF term. " ++
                 "See https://www.w3.org/TR/shacl/#HasValueConstraintComponent") $
            set $ rdf "Node",

          "in">:
            doc ("Specifies the condition that each value node is a member of a provided SHACL list. " ++
                 "See https://www.w3.org/TR/shacl/#InConstraintComponent") $
            list $ rdf "Node",

          "languageIn">:
            see "https://www.w3.org/TR/shacl/#LanguageInConstraintComponent" $
            set $ rdf "LanguageTag",

          "nodeKind">:
            see "https://www.w3.org/TR/shacl/#NodeKindConstraintComponent" $
            shacl "NodeKind",

          "node">:
            see "https://www.w3.org/TR/shacl/#NodeConstraintComponent" $
            set $ shacl "Reference" @@ shacl "NodeShape",

          "not">:
            see "https://www.w3.org/TR/shacl/#NotConstraintComponent" $
            set $ shacl "Reference" @@ shacl "Shape",

          "maxExclusive">:
            see "https://www.w3.org/TR/shacl/#MaxExclusiveConstraintComponent" $
            rdf "Literal",

          "maxInclusive">:
            see "https://www.w3.org/TR/shacl/#MaxInclusiveConstraintComponent" $
            rdf "Literal",

          "maxLength">:
            see "https://www.w3.org/TR/shacl/#MaxLengthConstraintComponent" $
            bigint,

          "minExclusive">:
            see "https://www.w3.org/TR/shacl/#MinExclusiveConstraintComponent" $
            rdf "Literal",

          "minInclusive">:
            see "https://www.w3.org/TR/shacl/#MinInclusiveConstraintComponent" $
            rdf "Literal",

          "minLength">:
            see "https://www.w3.org/TR/shacl/#MinLengthConstraintComponent" $
            bigint,

          "pattern">:
            see "https://www.w3.org/TR/shacl/#PatternConstraintComponent" $
            shacl "Pattern",

          "property">:
            see "https://www.w3.org/TR/shacl/#PropertyConstraintComponent" $
            set $ shacl "Reference" @@ shacl "PropertyShape",

          "or">:
            see "https://www.w3.org/TR/shacl/#OrConstraintComponent" $
            set $ shacl "Reference" @@ shacl "Shape",

          "xone">:
            see "https://www.w3.org/TR/shacl/#XoneConstraintComponent" $
            set $ shacl "Reference" @@ shacl "Shape"],

      def "CommonProperties" $
        doc "Common constraint parameters and other properties for SHACL shapes" $
        record [
          "constraints">:
            doc "Common constraint parameters attached to this shape"
            $ set $ shacl "CommonConstraint",

          "deactivated">:
            see "https://www.w3.org/TR/shacl/#deactivated" $
            optional boolean,

          "message">:
            see "https://www.w3.org/TR/shacl/#message" $
            rdf "LangStrings",

          "severity">:
            see "https://www.w3.org/TR/shacl/#severity" $
            shacl "Severity",

          "targetClass">:
            see "https://www.w3.org/TR/shacl/#targetClass" $
            set $ rdf "RdfsClass",

          "targetNode">:
            see "https://www.w3.org/TR/shacl/#targetNode" $
            set $ rdf "IriOrLiteral",

          "targetObjectsOf">:
            see "https://www.w3.org/TR/shacl/#targetObjectsOf" $
            set $ rdf "Property",

          "targetSubjectsOf">:
            see "https://www.w3.org/TR/shacl/#targetSubjectsOf" $
            set $ rdf "Property"],

      def "Definition" $
        doc "An instance of a type like sh:Shape or sh:NodeShape, together with a unique IRI for that instance" $
        lambda "a" $ record [
          "iri">: rdf "Iri",
          "target">: "a"],

      def "NodeKind" $ union [
        "blankNode">: doc "A blank node" unit,
        "iri">: doc "An IRI" unit,
        "literal">: doc "A literal" unit,
        "blankNodeOrIri">: doc "A blank node or an IRI" unit,
        "blankNodeOrLiteral">: doc "A blank node or a literal" unit,
        "iriOrLiteral">: doc "An IRI or a literal" unit],

      def "NodeShape" $
        doc "A SHACL node shape. See https://www.w3.org/TR/shacl/#node-shapes" $
        record [
          "common">: shacl "CommonProperties"],

      def "Pattern" $
        doc "A SHACL pattern. See https://www.w3.org/TR/shacl/#PatternConstraintComponent" $
        record [
          "regex">: string,
          "flags">: optional string],

      def "PropertyShape" $
        doc "A SHACL property shape. See https://www.w3.org/TR/shacl/#property-shapes" $
        record [
          "common">: shacl "CommonProperties",

          "constraints">:
            doc "Any property shape -specific constraint parameters" $
            set $ shacl "PropertyShapeConstraint",

          "defaultValue">:
            see "https://www.w3.org/TR/shacl/#defaultValue" $
            optional $ rdf "Node",

          "description">:
            see "https://www.w3.org/TR/shacl/#name" $
            rdf "LangStrings",

          "name">:
            see "https://www.w3.org/TR/shacl/#name" $
            rdf "LangStrings",

          "order">:
            see "https://www.w3.org/TR/shacl/#order" $
            optional bigint,

          "path">: rdf "Iri"], -- TODO
          -- Note: sh:group is omitted for now, for lack of a clear definition of PropertyGroup

      def "PropertyShapeConstraint" $
        doc "A number of constraint parameters which are specific to property shapes, and cannot be applied to node shapes" $
        union [

          "lessThan">:
            see "https://www.w3.org/TR/shacl/#LessThanConstraintComponent" $
            set $ rdf "Property",

          "lessThanOrEquals">:
            see "https://www.w3.org/TR/shacl/#LessThanOrEqualsConstraintComponent" $
            set $ rdf "Property",

          "maxCount">:
            doc ("The maximum cardinality. Node shapes cannot have any value for sh:maxCount. " ++
                 "See https://www.w3.org/TR/shacl/#MaxCountConstraintComponent") $
            bigint,

          "minCount">:
            doc ("The minimum cardinality. Node shapes cannot have any value for sh:minCount. " ++
                 "See https://www.w3.org/TR/shacl/#MinCountConstraintComponent") $
            bigint,

          "uniqueLang">:
            see "https://www.w3.org/TR/shacl/#UniqueLangConstraintComponent" $
            boolean,

          "qualifiedValueShape">:
            see "https://www.w3.org/TR/shacl/#QualifiedValueShapeConstraintComponent" $
            shacl "QualifiedValueShape"],

      def "QualifiedValueShape" $
        see "https://www.w3.org/TR/shacl/#QualifiedValueShapeConstraintComponent" $
        record [
          "qualifiedValueShape">: shacl "Reference" @@ shacl "Shape",
          "qualifiedMaxCount">: bigint,
          "qualifiedMinCount">: bigint,
          "qualifiedValueShapesDisjoint">: optional boolean],

      def "Reference" $
        doc "Either an instance of a type like sh:Shape or sh:NodeShape, or an IRI which refers to an instance of that type" $
        lambda "a" $ union [
          "named">: rdf "Iri",
          "anonymous">:
            doc "An anonymous instance"
            "a",
          "definition">:
            doc "An inline definition" $
            shacl "Definition" @@ "a"],

      def "Severity" $ union [
        "info">: doc "A non-critical constraint violation indicating an informative message" unit,
        "warning">: doc "A non-critical constraint violation indicating a warning" unit,
        "violation">: doc "A constraint violation" unit],

      def "Shape" $
        doc "A SHACL node or property shape. See https://www.w3.org/TR/shacl/#shapes" $
        union [
          "node">: shacl "NodeShape",
          "property">: shacl "PropertyShape"],

      def "ShapesGraph" $
        doc ("An RDF graph containing zero or more shapes that is passed into a SHACL validation process " ++
             "so that a data graph can be validated against the shapes") $
        set $ shacl "Definition" @@ shacl "Shape"]
