module Hydra.Sources.Tier4.Langs.Owl.Syntax where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Sources.Tier4.Langs.Rdf.Syntax
import Hydra.Sources.Tier4.Langs.Xml.Schema
import Hydra.Dsl.Types as Types
import qualified Hydra.Dsl.Terms as Terms


key_iri :: String
key_iri = "iri"

withIri :: String -> Type -> Type
withIri iriStr = annotateType key_iri (Just $ Terms.string iriStr)

nonNegativeInteger :: Type
nonNegativeInteger = Types.bigint

owlIri :: [Char] -> Type -> Type
owlIri local = withIri $ "http://www.w3.org/2002/07/owl#" ++ local

owlSyntaxModule :: Module
owlSyntaxModule = Module ns elements [rdfSyntaxModule, xmlSchemaModule] $
    Just "An OWL 2 syntax model. See https://www.w3.org/TR/owl2-syntax"
  where
    ns = Namespace "hydra/langs/owl/syntax"
    def = datatype ns

    owl = typeref ns
    rdf = typeref $ moduleNamespace rdfSyntaxModule
    xsd = typeref $ moduleNamespace xmlSchemaModule

    objectPropertyConstraint lname = def lname $ record [
      "annotations">: list $ owl "Annotation",
      "property">: owl "ObjectPropertyExpression"]

    simpleUnion names = union $ (\n -> FieldType (Name $ decapitalize n) $ owl n) <$> names

    withAnns fields = record $
      ("annotations">: list (owl "Annotation")):fields

    elements = generalDefinitions ++ owl2Definitions -- ++ instances

--    instances = [
--      inst "Nothing" (owl "Class") Terms.unit,
--      inst "Thing" (owl "Class") Terms.unit]

    generalDefinitions = [
-- nonNegativeInteger := a nonempty finite sequence of digits between 0 and 9
-- quotedString := a finite sequence of characters in which " (U+22) and \ (U+5C) occur only in pairs of the form \" (U+5C, U+22) and \\ (U+5C, U+5C), enclosed in a pair of " (U+22) characters
-- languageTag := @ (U+40) followed a nonempty sequence of characters matching the langtag production from [BCP 47]
-- nodeID := a finite sequence of characters matching the BLANK_NODE_LABEL production of [SPARQL]
-- fullIRI := an IRI as defined in [RFC3987], enclosed in a pair of < (U+3C) and > (U+3E) characters
-- prefixName := a finite sequence of characters matching the as PNAME_NS production of [SPARQL]
-- abbreviatedIRI := a finite sequence of characters matching the PNAME_LN production of [SPARQL]
-- IRI := fullIRI | abbreviatedIRI
-- ontologyDocument := { prefixDeclaration } Ontology
-- prefixDeclaration := 'Prefix' '(' prefixName '=' fullIRI ')'

-- Ontology :=
--     'Ontology' '(' [ ontologyIRI [ versionIRI ] ]
--        directlyImportsDocuments
--        ontologyAnnotations
--        axioms
--     ')'
      def "Ontology" $ record [ -- note: omitting IRI and version
        "directImports">: list $ owl "Ontology",
        "annotations">: list $ owl "Annotation",
        "axioms">: list $ owl "Axiom"],

-- ontologyIRI := IRI
-- versionIRI := IRI
-- directlyImportsDocuments := { 'Import' '(' IRI ')' }
-- ontologyAnnotations := { Annotation }
-- axioms := { Axiom }

-- Declaration := 'Declaration' '(' axiomAnnotations Entity ')'
      def "Declaration" $ withAnns [
        "entity">: owl "Entity"],

-- Entity :=
--     'Class' '(' Class ')' |
--     'Datatype' '(' Datatype ')' |
--     'ObjectProperty' '(' ObjectProperty ')' |
--     'DataProperty' '(' DataProperty ')' |
--     'AnnotationProperty' '(' AnnotationProperty ')' |
--     'NamedIndividual' '(' NamedIndividual ')'
      def "Entity" $ simpleUnion [
        "AnnotationProperty",
        "Class",
        "DataProperty",
        "Datatype",
        "NamedIndividual",
        "ObjectProperty"],

-- AnnotationSubject := IRI | AnonymousIndividual
      def "AnnotationSubject" $ union [
        "iri">: rdf "Iri",
        "anonymousIndividual">: owl "AnonymousIndividual"],

-- AnnotationValue := AnonymousIndividual | IRI | Literal
      def "AnnotationValue" $ union [
        "anonymousIndividual">: owl "AnonymousIndividual",
        "iri">: rdf "Iri",
        "literal">: rdf "Literal"],

-- axiomAnnotations := { Annotation }

-- Annotation := 'Annotation' '(' annotationAnnotations AnnotationProperty AnnotationValue ')'
      def "Annotation" $ withAnns [
        "property">: owl "AnnotationProperty",
        "value">: owl "AnnotationValue"],

-- annotationAnnotations  := { Annotation }

-- AnnotationAxiom := AnnotationAssertion | SubAnnotationPropertyOf | AnnotationPropertyDomain | AnnotationPropertyRange
      def "AnnotationAxiom" $ simpleUnion [
        "AnnotationAssertion",
        "AnnotationPropertyDomain",
        "AnnotationPropertyRange",
        "SubAnnotationPropertyOf"],

-- AnnotationAssertion := 'AnnotationAssertion' '(' axiomAnnotations AnnotationProperty AnnotationSubject AnnotationValue ')'
      def "AnnotationAssertion" $ withAnns [
        "property">: owl "AnnotationProperty",
        "subject">: owl "AnnotationSubject",
        "value">: owl "AnnotationValue"],

-- SubAnnotationPropertyOf := 'SubAnnotationPropertyOf' '(' axiomAnnotations subAnnotationProperty superAnnotationProperty ')'
      def "SubAnnotationPropertyOf" $ withAnns [
        "subProperty">: owl "AnnotationProperty",
        "superProperty">: owl "AnnotationProperty"],

-- subAnnotationProperty := AnnotationProperty
-- superAnnotationProperty := AnnotationProperty

-- AnnotationPropertyDomain := 'AnnotationPropertyDomain' '(' axiomAnnotations AnnotationProperty IRI ')'
      def "AnnotationPropertyDomain" $ withAnns [
        "property">: owl "AnnotationProperty",
        "iri">: rdf "Iri"],

-- AnnotationPropertyRange := 'AnnotationPropertyRange' '(' axiomAnnotations AnnotationProperty IRI ')'
      def "AnnotationPropertyRange" $ withAnns [
        "property">: owl "AnnotationProperty",
        "iri">: rdf "Iri"]]

    owl2Definitions = [
-- Class := IRI
      def "Class" $
        see "https://www.w3.org/TR/owl2-syntax/#Classes" unit,

-- Datatype := IRI
      def "Datatype" $
        see "https://www.w3.org/TR/owl2-syntax/#Datatypes" $
        union [
          "xmlSchema">:
            note ("XML Schema datatypes are treated as a special case in this model " ++
                  "(not in the OWL 2 specification itself) because they are particularly common") $
            xsd "Datatype",
          "other">: rdf "Iri"],

-- ObjectProperty := IRI
      def "ObjectProperty" $
        see "https://www.w3.org/TR/owl2-syntax/#Object_Properties" unit,

-- DataProperty := IRI
      def "DataProperty" unit,

-- AnnotationProperty := IRI
      def "AnnotationProperty" unit,

-- Individual := NamedIndividual | AnonymousIndividual
      def "Individual" $ union [
        "named">: owl "NamedIndividual",
        "anonymous">: owl "AnonymousIndividual"],

-- NamedIndividual := IRI
      def "NamedIndividual" unit,

-- AnonymousIndividual := nodeID
      def "AnonymousIndividual" unit,

-- Literal := typedLiteral | stringLiteralNoLanguage | stringLiteralWithLanguage
-- typedLiteral := lexicalForm '^^' Datatype
-- lexicalForm := quotedString
-- stringLiteralNoLanguage := quotedString
-- stringLiteralWithLanguage := quotedString languageTag

-- ObjectPropertyExpression := ObjectProperty | InverseObjectProperty
      def "ObjectPropertyExpression" $ union [
        "object">: owl "ObjectProperty",
        "inverseObject">: owl "InverseObjectProperty"],

-- InverseObjectProperty := 'ObjectInverseOf' '(' ObjectProperty ')'
      def "InverseObjectProperty" $ owl "ObjectProperty",

-- DataPropertyExpression := DataProperty
      def "DataPropertyExpression" $ owl "DataProperty",

-- DataRange :=
--     Datatype |
--     DataIntersectionOf |
--     DataUnionOf |
--     DataComplementOf |
--     DataOneOf |
--     DatatypeRestriction
      def "DataRange" $
        see "https://www.w3.org/TR/owl2-syntax/#Data_Ranges" $
        simpleUnion [
          "DataComplementOf",
          "DataIntersectionOf",
          "DataOneOf",
          "DataUnionOf",
          "Datatype",
          "DatatypeRestriction"],

-- DataIntersectionOf := 'DataIntersectionOf' '(' DataRange DataRange { DataRange } ')'
      def "DataIntersectionOf" $
        see "https://www.w3.org/TR/owl2-syntax/#Intersection_of_Data_Ranges" $
        twoOrMoreList $ owl "DataRange",

-- DataUnionOf := 'DataUnionOf' '(' DataRange DataRange { DataRange } ')'
      def "DataUnionOf" $
        see "https://www.w3.org/TR/owl2-syntax/#Union_of_Data_Ranges" $
        twoOrMoreList $ owl "DataRange",

-- DataComplementOf := 'DataComplementOf' '(' DataRange ')'
      def "DataComplementOf" $
        see "https://www.w3.org/TR/owl2-syntax/#Complement_of_Data_Ranges" $
        owl "DataRange",

-- DataOneOf := 'DataOneOf' '(' Literal { Literal } ')'
      def "DataOneOf" $
        see "https://www.w3.org/TR/owl2-syntax/#Enumeration_of_Literals" $
        nonemptyList $ rdf "Literal",

-- DatatypeRestriction := 'DatatypeRestriction' '(' Datatype constrainingFacet restrictionValue { constrainingFacet restrictionValue } ')'
-- constrainingFacet := IRI
-- restrictionValue := Literal
      def "DatatypeRestriction" $
        see "https://www.w3.org/TR/owl2-syntax/#Datatype_Restrictions" $
        record [
          "datatype">: owl "Datatype",
          "constraints">: nonemptyList $ owl "DatatypeRestriction.Constraint"],

      def "DatatypeRestriction.Constraint" $ record [
        "constrainingFacet">: owl "DatatypeRestriction.ConstrainingFacet",
        "restrictionValue">: rdf "Literal"],

      def "DatatypeRestriction.ConstrainingFacet" $
        union [
          "xmlSchema">:
            note ("XML Schema constraining facets are treated as a special case in this model " ++
                  "(not in the OWL 2 specification itself) because they are particularly common") $
            xsd "ConstrainingFacet",
          "other">: rdf "Iri"],

-- ClassExpression :=
--     Class |
--     ObjectIntersectionOf | ObjectUnionOf | ObjectComplementOf | ObjectOneOf |
--     ObjectSomeValuesFrom | ObjectAllValuesFrom | ObjectHasValue | ObjectHasSelf |
--     ObjectMinCardinality | ObjectMaxCardinality | ObjectExactCardinality |
--     DataSomeValuesFrom | DataAllValuesFrom | DataHasValue |
--     DataMinCardinality | DataMaxCardinality | DataExactCardinality
      def "ClassExpression" $ simpleUnion [
        "Class",
        "DataSomeValuesFrom",
        "DataAllValuesFrom",
        "DataHasValue",
        "DataMinCardinality",
        "DataMaxCardinality",
        "DataExactCardinality",
        "ObjectAllValuesFrom",
        "ObjectExactCardinality",
        "ObjectHasSelf",
        "ObjectHasValue",
        "ObjectIntersectionOf",
        "ObjectMaxCardinality",
        "ObjectMinCardinality",
        "ObjectOneOf",
        "ObjectSomeValuesFrom",
        "ObjectUnionOf"],

-- ObjectIntersectionOf := 'ObjectIntersectionOf' '(' ClassExpression ClassExpression { ClassExpression } ')'
      def "ObjectIntersectionOf" $ twoOrMoreList $ owl "ClassExpression",

-- ObjectUnionOf := 'ObjectUnionOf' '(' ClassExpression ClassExpression { ClassExpression } ')'
      def "ObjectUnionOf" $ twoOrMoreList $ owl "ClassExpression",

-- ObjectComplementOf := 'ObjectComplementOf' '(' ClassExpression ')'
      def "ObjectComplementOf" $ owl "ClassExpression",

-- ObjectOneOf := 'ObjectOneOf' '(' Individual { Individual }')'
      def "ObjectOneOf" $ nonemptyList $ owl "Individual",

-- ObjectSomeValuesFrom := 'ObjectSomeValuesFrom' '(' ObjectPropertyExpression ClassExpression ')'
      def "ObjectSomeValuesFrom" $ record [
        "property">: owl "ObjectPropertyExpression",
        "class">: owl "ClassExpression"],

-- ObjectAllValuesFrom := 'ObjectAllValuesFrom' '(' ObjectPropertyExpression ClassExpression ')'
      def "ObjectAllValuesFrom" $ record [
        "property">: owl "ObjectPropertyExpression",
        "class">: owl "ClassExpression"],

-- ObjectHasValue := 'ObjectHasValue' '(' ObjectPropertyExpression Individual ')'
      def "ObjectHasValue" $ record [
        "property">: owl "ObjectPropertyExpression",
        "individual">: owl "Individual"],

-- ObjectHasSelf := 'ObjectHasSelf' '(' ObjectPropertyExpression ')'
      def "ObjectHasSelf" $ owl "ObjectPropertyExpression",

-- ObjectMinCardinality := 'ObjectMinCardinality' '(' nonNegativeInteger ObjectPropertyExpression [ ClassExpression ] ')'
      def "ObjectMinCardinality" $
        see "https://www.w3.org/TR/owl2-syntax/#Minimum_Cardinality" $
        record [
          "bound">: nonNegativeInteger,
          "property">: owl "ObjectPropertyExpression",
          "class">: list $ owl "ClassExpression"],

-- ObjectMaxCardinality := 'ObjectMaxCardinality' '(' nonNegativeInteger ObjectPropertyExpression [ ClassExpression ] ')'
      def "ObjectMaxCardinality" $
        see "https://www.w3.org/TR/owl2-syntax/#Maximum_Cardinality" $
        record [
          "bound">: nonNegativeInteger,
          "property">: owl "ObjectPropertyExpression",
          "class">: list $ owl "ClassExpression"],

-- ObjectExactCardinality := 'ObjectExactCardinality' '(' nonNegativeInteger ObjectPropertyExpression [ ClassExpression ] ')'
      def "ObjectExactCardinality" $
        see "https://www.w3.org/TR/owl2-syntax/#Exact_Cardinality" $
        record [
          "bound">: nonNegativeInteger,
          "property">: owl "ObjectPropertyExpression",
          "class">: list $ owl "ClassExpression"],

-- DataSomeValuesFrom := 'DataSomeValuesFrom' '(' DataPropertyExpression { DataPropertyExpression } DataRange ')'
      def "DataSomeValuesFrom" $ record [
        "property">: nonemptyList $ owl "DataPropertyExpression",
        "range">: owl "DataRange"],

-- DataAllValuesFrom := 'DataAllValuesFrom' '(' DataPropertyExpression { DataPropertyExpression } DataRange ')'
      def "DataAllValuesFrom" $ record [
        "property">: nonemptyList $ owl "DataPropertyExpression",
        "range">: owl "DataRange"],

-- DataHasValue := 'DataHasValue' '(' DataPropertyExpression Literal ')'
      def "DataHasValue" $ record [
        "property">: owl "DataPropertyExpression",
        "value">: rdf "Literal"],

-- DataMinCardinality := 'DataMinCardinality' '(' nonNegativeInteger DataPropertyExpression [ DataRange ] ')'
      def "DataMinCardinality" $ record [
        "bound">: nonNegativeInteger,
        "property">: owl "DataPropertyExpression",
        "range">: list $ owl "DataRange"],

-- DataMaxCardinality := 'DataMaxCardinality' '(' nonNegativeInteger DataPropertyExpression [ DataRange ] ')'
      def "DataMaxCardinality" $ record [
        "bound">: nonNegativeInteger,
        "property">: owl "DataPropertyExpression",
        "range">: list $ owl "DataRange"],

-- DataExactCardinality := 'DataExactCardinality' '(' nonNegativeInteger DataPropertyExpression [ DataRange ] ')'
      def "DataExactCardinality" $ record [
        "bound">: nonNegativeInteger,
        "property">: owl "DataPropertyExpression",
        "range">: list $ owl "DataRange"],

-- Axiom := Declaration | ClassAxiom | ObjectPropertyAxiom | DataPropertyAxiom | DatatypeDefinition | HasKey | Assertion | AnnotationAxiom
      def "Axiom" $
        see "https://www.w3.org/TR/owl2-syntax/#Axioms" $
        simpleUnion [
          "AnnotationAxiom",
          "Assertion",
          "ClassAxiom",
          "DataPropertyAxiom",
          "DatatypeDefinition",
          "Declaration",
          "HasKey",
          "ObjectPropertyAxiom"],

-- ClassAxiom := SubClassOf | EquivalentClasses | DisjointClasses | DisjointUnion
      def "ClassAxiom" $ simpleUnion [
        "DisjointClasses",
        "DisjointUnion",
        "EquivalentClasses",
        "SubClassOf"],

-- SubClassOf := 'SubClassOf' '(' axiomAnnotations subClassExpression superClassExpression ')'
-- subClassExpression := ClassExpression
-- superClassExpression := ClassExpression
      def "SubClassOf" $ withAnns [
        "subClass">: owl "ClassExpression",
        "superClass">: owl "ClassExpression"],

-- EquivalentClasses := 'EquivalentClasses' '(' axiomAnnotations ClassExpression ClassExpression { ClassExpression } ')'
      def "EquivalentClasses" $ withAnns [
        "classes">: twoOrMoreList $ owl "ClassExpression"],

-- DisjointClasses := 'DisjointClasses' '(' axiomAnnotations ClassExpression ClassExpression { ClassExpression } ')'
      def "DisjointClasses" $ withAnns [
        "classes">: twoOrMoreList $ owl "ClassExpression"],

-- DisjointUnion := 'DisjointUnion' '(' axiomAnnotations Class disjointClassExpressions ')'
-- disjointClassExpressions := ClassExpression ClassExpression { ClassExpression }
      def "DisjointUnion" $
        see "https://www.w3.org/TR/owl2-syntax/#Disjoint_Union_of_Class_Expressions" $
        withAnns [
          "class">: owl "Class",
          "classes">: twoOrMoreList $ owl "ClassExpression"],

-- ObjectPropertyAxiom :=
--     SubObjectPropertyOf | EquivalentObjectProperties |
--     DisjointObjectProperties | InverseObjectProperties |
--     ObjectPropertyDomain | ObjectPropertyRange |
--     FunctionalObjectProperty | InverseFunctionalObjectProperty |
--     ReflexiveObjectProperty | IrreflexiveObjectProperty |
--     SymmetricObjectProperty | AsymmetricObjectProperty |
--     TransitiveObjectProperty
      def "ObjectPropertyAxiom" $ simpleUnion [
        "AsymmetricObjectProperty",
        "DisjointObjectProperties",
        "EquivalentObjectProperties",
        "FunctionalObjectProperty",
        "InverseFunctionalObjectProperty",
        "InverseObjectProperties",
        "IrreflexiveObjectProperty",
        "ObjectPropertyDomain",
        "ObjectPropertyRange",
        "ReflexiveObjectProperty",
        "SubObjectPropertyOf",
        "SymmetricObjectProperty",
        "TransitiveObjectProperty"],

-- SubObjectPropertyOf := 'SubObjectPropertyOf' '(' axiomAnnotations subObjectPropertyExpression superObjectPropertyExpression ')'
      def "SubObjectPropertyOf" $ withAnns [
        "subProperty">: nonemptyList $ owl "ObjectPropertyExpression",
        "superProperty">: owl "ObjectPropertyExpression"],
-- subObjectPropertyExpression := ObjectPropertyExpression | propertyExpressionChain
-- propertyExpressionChain := 'ObjectPropertyChain' '(' ObjectPropertyExpression ObjectPropertyExpression { ObjectPropertyExpression } ')'
-- superObjectPropertyExpression := ObjectPropertyExpression

-- EquivalentObjectProperties := 'EquivalentObjectProperties' '(' axiomAnnotations ObjectPropertyExpression ObjectPropertyExpression { ObjectPropertyExpression } ')'
      def "EquivalentObjectProperties" $ withAnns [
        "properties">: twoOrMoreList $ owl "ObjectPropertyExpression"],

-- DisjointObjectProperties := 'DisjointObjectProperties' '(' axiomAnnotations ObjectPropertyExpression ObjectPropertyExpression { ObjectPropertyExpression } ')'
      def "DisjointObjectProperties" $ withAnns [
        "properties">: twoOrMoreList $ owl "ObjectPropertyExpression"],

-- ObjectPropertyDomain := 'ObjectPropertyDomain' '(' axiomAnnotations ObjectPropertyExpression ClassExpression ')'
      def "ObjectPropertyDomain" $
        see "https://www.w3.org/TR/owl2-syntax/#Object_Property_Domain" $
        withAnns [
          "property">: owl "ObjectPropertyExpression",
          "domain">: owl "ClassExpression"],

-- ObjectPropertyRange := 'ObjectPropertyRange' '(' axiomAnnotations ObjectPropertyExpression ClassExpression ')'
      def "ObjectPropertyRange" $
        see "https://www.w3.org/TR/owl2-syntax/#Object_Property_Range" $
        withAnns [
          "property">: owl "ObjectPropertyExpression",
          "range">: owl "ClassExpression"],

-- InverseObjectProperties := 'InverseObjectProperties' '(' axiomAnnotations ObjectPropertyExpression ObjectPropertyExpression ')'
      def "InverseObjectProperties" $ withAnns [
        "property1">: owl "ObjectPropertyExpression",
        "property2">: owl "ObjectPropertyExpression"],

-- FunctionalObjectProperty := 'FunctionalObjectProperty' '(' axiomAnnotations ObjectPropertyExpression ')'
      objectPropertyConstraint "FunctionalObjectProperty",

-- InverseFunctionalObjectProperty := 'InverseFunctionalObjectProperty' '(' axiomAnnotations ObjectPropertyExpression ')'
      objectPropertyConstraint "InverseFunctionalObjectProperty",

-- ReflexiveObjectProperty := 'ReflexiveObjectProperty' '(' axiomAnnotations ObjectPropertyExpression ')'
      objectPropertyConstraint "ReflexiveObjectProperty",

-- IrreflexiveObjectProperty := 'IrreflexiveObjectProperty' '(' axiomAnnotations ObjectPropertyExpression ')'
      objectPropertyConstraint "IrreflexiveObjectProperty",

-- SymmetricObjectProperty := 'SymmetricObjectProperty' '(' axiomAnnotations ObjectPropertyExpression ')'
      objectPropertyConstraint "SymmetricObjectProperty",

-- AsymmetricObjectProperty := 'AsymmetricObjectProperty' '(' axiomAnnotations ObjectPropertyExpression ')'
      objectPropertyConstraint "AsymmetricObjectProperty",

-- TransitiveObjectProperty := 'TransitiveObjectProperty' '(' axiomAnnotations ObjectPropertyExpression ')'
      objectPropertyConstraint "TransitiveObjectProperty",

-- DataPropertyAxiom :=
--     SubDataPropertyOf | EquivalentDataProperties | DisjointDataProperties |
--     DataPropertyDomain | DataPropertyRange | FunctionalDataProperty
      def "DataPropertyAxiom" $ simpleUnion [
        "DataPropertyAxiom",
        "DataPropertyRange",
        "DisjointDataProperties",
        "EquivalentDataProperties",
        "FunctionalDataProperty",
        "SubDataPropertyOf"],

-- SubDataPropertyOf := 'SubDataPropertyOf' '(' axiomAnnotations subDataPropertyExpression superDataPropertyExpression ')'
      def "SubDataPropertyOf" $ withAnns [
        "subProperty">: owl "DataPropertyExpression",
        "superProperty">: owl "DataPropertyExpression"],
-- subDataPropertyExpression := DataPropertyExpression
-- superDataPropertyExpression := DataPropertyExpression

-- EquivalentDataProperties := 'EquivalentDataProperties' '(' axiomAnnotations DataPropertyExpression DataPropertyExpression { DataPropertyExpression } ')'
      def "EquivalentDataProperties" $ withAnns [
        "properties">: twoOrMoreList $ owl "DataPropertyExpression"],

-- DisjointDataProperties := 'DisjointDataProperties' '(' axiomAnnotations DataPropertyExpression DataPropertyExpression { DataPropertyExpression } ')'
      def "DisjointDataProperties" $ withAnns [
        "properties">: twoOrMoreList $ owl "DataPropertyExpression"],

-- DataPropertyDomain := 'DataPropertyDomain' '(' axiomAnnotations DataPropertyExpression ClassExpression ')'
      def "DataPropertyDomain" $ withAnns [
        "property">: owl "DataPropertyExpression",
        "domain">: owl "ClassExpression"],

-- DataPropertyRange := 'DataPropertyRange' '(' axiomAnnotations DataPropertyExpression DataRange ')'
      def "DataPropertyRange" $ withAnns [
        "property">: owl "DataPropertyExpression",
        "range">: owl "ClassExpression"],

-- FunctionalDataProperty := 'FunctionalDataProperty' '(' axiomAnnotations DataPropertyExpression ')'
      def "FunctionalDataProperty" $ withAnns [
        "property">: owl "DataPropertyExpression"],

-- DatatypeDefinition := 'DatatypeDefinition' '(' axiomAnnotations Datatype DataRange ')'
      def "DatatypeDefinition" $ withAnns [
        "datatype">: owl "Datatype",
        "range">: owl "DataRange"],

-- HasKey := 'HasKey' '(' axiomAnnotations ClassExpression '(' { ObjectPropertyExpression } ')' '(' { DataPropertyExpression } ')' ')'
      def "HasKey" $
        see "https://www.w3.org/TR/owl2-syntax/#Keys" $
        withAnns [
          "class">: owl "ClassExpression",
          "objectProperties">: list $ owl "ObjectPropertyExpression",
          "dataProperties">: list $ owl "DataPropertyExpression"],

-- Assertion :=
--     SameIndividual | DifferentIndividuals | ClassAssertion |
--     ObjectPropertyAssertion | NegativeObjectPropertyAssertion |
--     DataPropertyAssertion | NegativeDataPropertyAssertion
      def "Assertion" $ simpleUnion [
       "ClassAssertion",
       "DataPropertyAssertion",
       "DifferentIndividuals",
       "ObjectPropertyAssertion",
       "NegativeDataPropertyAssertion",
       "NegativeObjectPropertyAssertion",
       "SameIndividual"],

-- sourceIndividual := Individual
-- targetIndividual := Individual
-- targetValue := Literal
-- SameIndividual := 'SameIndividual' '(' axiomAnnotations Individual Individual { Individual } ')'
      def "SameIndividual" $ withAnns [
        "individuals">: twoOrMoreList $ owl "Individual"],

-- DifferentIndividuals := 'DifferentIndividuals' '(' axiomAnnotations Individual Individual { Individual } ')'
      def "DifferentIndividuals" $ withAnns [
        "individuals">: twoOrMoreList $ owl "Individual"],

-- ClassAssertion := 'ClassAssertion' '(' axiomAnnotations ClassExpression Individual ')'
      def "ClassAssertion"$ withAnns [
        "class">: owl "ClassExpression",
        "individual">: owl "Individual"],

-- ObjectPropertyAssertion := 'ObjectPropertyAssertion' '(' axiomAnnotations ObjectPropertyExpression sourceIndividual targetIndividual ')'
      def "ObjectPropertyAssertion" $ withAnns [
        "property">: owl "ObjectPropertyExpression",
        "source">: owl "Individual",
        "target">: owl "Individual"],

-- NegativeObjectPropertyAssertion := 'NegativeObjectPropertyAssertion' '(' axiomAnnotations ObjectPropertyExpression sourceIndividual targetIndividual ')'
      def "NegativeObjectPropertyAssertion" $ withAnns [
        "property">: owl "ObjectPropertyExpression",
        "source">: owl "Individual",
        "target">: owl "Individual"],

-- DataPropertyAssertion := 'DataPropertyAssertion' '(' axiomAnnotations DataPropertyExpression sourceIndividual targetValue ')'
      def "DataPropertyAssertion" $ withAnns [
        "property">: owl "DataPropertyExpression",
        "source">: owl "Individual",
        "target">: owl "Individual"],

-- NegativeDataPropertyAssertion := 'NegativeDataPropertyAssertion' '(' axiomAnnotations DataPropertyExpression sourceIndividual targetValue ')'
      def "NegativeDataPropertyAssertion" $ withAnns [
        "property">: owl "DataPropertyExpression",
        "source">: owl "Individual",
        "target">: owl "Individual"]]
