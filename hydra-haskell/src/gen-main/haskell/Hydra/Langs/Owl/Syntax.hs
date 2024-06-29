-- | An OWL 2 syntax model. See https://www.w3.org/TR/owl2-syntax

module Hydra.Langs.Owl.Syntax where

import qualified Hydra.Core as Core
import qualified Hydra.Langs.Rdf.Syntax as Syntax
import qualified Hydra.Langs.Xml.Schema as Schema
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

data Ontology = 
  Ontology {
    ontologyDirectImports :: [Ontology],
    ontologyAnnotations :: [Annotation],
    ontologyAxioms :: [Axiom]}
  deriving (Eq, Ord, Read, Show)

_Ontology = (Core.Name "hydra/langs/owl/syntax.Ontology")

_Ontology_directImports = (Core.Name "directImports")

_Ontology_annotations = (Core.Name "annotations")

_Ontology_axioms = (Core.Name "axioms")

data Declaration = 
  Declaration {
    declarationAnnotations :: [Annotation],
    declarationEntity :: Entity}
  deriving (Eq, Ord, Read, Show)

_Declaration = (Core.Name "hydra/langs/owl/syntax.Declaration")

_Declaration_annotations = (Core.Name "annotations")

_Declaration_entity = (Core.Name "entity")

data Entity = 
  EntityAnnotationProperty AnnotationProperty |
  EntityClass Class |
  EntityDataProperty DataProperty |
  EntityDatatype Datatype |
  EntityNamedIndividual NamedIndividual |
  EntityObjectProperty ObjectProperty
  deriving (Eq, Ord, Read, Show)

_Entity = (Core.Name "hydra/langs/owl/syntax.Entity")

_Entity_annotationProperty = (Core.Name "annotationProperty")

_Entity_class = (Core.Name "class")

_Entity_dataProperty = (Core.Name "dataProperty")

_Entity_datatype = (Core.Name "datatype")

_Entity_namedIndividual = (Core.Name "namedIndividual")

_Entity_objectProperty = (Core.Name "objectProperty")

data AnnotationSubject = 
  AnnotationSubjectIri Syntax.Iri |
  AnnotationSubjectAnonymousIndividual AnonymousIndividual
  deriving (Eq, Ord, Read, Show)

_AnnotationSubject = (Core.Name "hydra/langs/owl/syntax.AnnotationSubject")

_AnnotationSubject_iri = (Core.Name "iri")

_AnnotationSubject_anonymousIndividual = (Core.Name "anonymousIndividual")

data AnnotationValue = 
  AnnotationValueAnonymousIndividual AnonymousIndividual |
  AnnotationValueIri Syntax.Iri |
  AnnotationValueLiteral Syntax.Literal
  deriving (Eq, Ord, Read, Show)

_AnnotationValue = (Core.Name "hydra/langs/owl/syntax.AnnotationValue")

_AnnotationValue_anonymousIndividual = (Core.Name "anonymousIndividual")

_AnnotationValue_iri = (Core.Name "iri")

_AnnotationValue_literal = (Core.Name "literal")

data Annotation = 
  Annotation {
    annotationAnnotations :: [Annotation],
    annotationProperty :: AnnotationProperty,
    annotationValue :: AnnotationValue}
  deriving (Eq, Ord, Read, Show)

_Annotation = (Core.Name "hydra/langs/owl/syntax.Annotation")

_Annotation_annotations = (Core.Name "annotations")

_Annotation_property = (Core.Name "property")

_Annotation_value = (Core.Name "value")

data AnnotationAxiom = 
  AnnotationAxiomAnnotationAssertion AnnotationAssertion |
  AnnotationAxiomAnnotationPropertyDomain AnnotationPropertyDomain |
  AnnotationAxiomAnnotationPropertyRange AnnotationPropertyRange |
  AnnotationAxiomSubAnnotationPropertyOf SubAnnotationPropertyOf
  deriving (Eq, Ord, Read, Show)

_AnnotationAxiom = (Core.Name "hydra/langs/owl/syntax.AnnotationAxiom")

_AnnotationAxiom_annotationAssertion = (Core.Name "annotationAssertion")

_AnnotationAxiom_annotationPropertyDomain = (Core.Name "annotationPropertyDomain")

_AnnotationAxiom_annotationPropertyRange = (Core.Name "annotationPropertyRange")

_AnnotationAxiom_subAnnotationPropertyOf = (Core.Name "subAnnotationPropertyOf")

data AnnotationAssertion = 
  AnnotationAssertion {
    annotationAssertionAnnotations :: [Annotation],
    annotationAssertionProperty :: AnnotationProperty,
    annotationAssertionSubject :: AnnotationSubject,
    annotationAssertionValue :: AnnotationValue}
  deriving (Eq, Ord, Read, Show)

_AnnotationAssertion = (Core.Name "hydra/langs/owl/syntax.AnnotationAssertion")

_AnnotationAssertion_annotations = (Core.Name "annotations")

_AnnotationAssertion_property = (Core.Name "property")

_AnnotationAssertion_subject = (Core.Name "subject")

_AnnotationAssertion_value = (Core.Name "value")

data SubAnnotationPropertyOf = 
  SubAnnotationPropertyOf {
    subAnnotationPropertyOfAnnotations :: [Annotation],
    subAnnotationPropertyOfSubProperty :: AnnotationProperty,
    subAnnotationPropertyOfSuperProperty :: AnnotationProperty}
  deriving (Eq, Ord, Read, Show)

_SubAnnotationPropertyOf = (Core.Name "hydra/langs/owl/syntax.SubAnnotationPropertyOf")

_SubAnnotationPropertyOf_annotations = (Core.Name "annotations")

_SubAnnotationPropertyOf_subProperty = (Core.Name "subProperty")

_SubAnnotationPropertyOf_superProperty = (Core.Name "superProperty")

data AnnotationPropertyDomain = 
  AnnotationPropertyDomain {
    annotationPropertyDomainAnnotations :: [Annotation],
    annotationPropertyDomainProperty :: AnnotationProperty,
    annotationPropertyDomainIri :: Syntax.Iri}
  deriving (Eq, Ord, Read, Show)

_AnnotationPropertyDomain = (Core.Name "hydra/langs/owl/syntax.AnnotationPropertyDomain")

_AnnotationPropertyDomain_annotations = (Core.Name "annotations")

_AnnotationPropertyDomain_property = (Core.Name "property")

_AnnotationPropertyDomain_iri = (Core.Name "iri")

data AnnotationPropertyRange = 
  AnnotationPropertyRange {
    annotationPropertyRangeAnnotations :: [Annotation],
    annotationPropertyRangeProperty :: AnnotationProperty,
    annotationPropertyRangeIri :: Syntax.Iri}
  deriving (Eq, Ord, Read, Show)

_AnnotationPropertyRange = (Core.Name "hydra/langs/owl/syntax.AnnotationPropertyRange")

_AnnotationPropertyRange_annotations = (Core.Name "annotations")

_AnnotationPropertyRange_property = (Core.Name "property")

_AnnotationPropertyRange_iri = (Core.Name "iri")

-- | See https://www.w3.org/TR/owl2-syntax/#Classes
data Class = 
  Class {}
  deriving (Eq, Ord, Read, Show)

_Class = (Core.Name "hydra/langs/owl/syntax.Class")

-- | See https://www.w3.org/TR/owl2-syntax/#Datatypes
data Datatype = 
  -- | Note: XML Schema datatypes are treated as a special case in this model (not in the OWL 2 specification itself) because they are particularly common
  DatatypeXmlSchema Schema.Datatype |
  DatatypeOther Syntax.Iri
  deriving (Eq, Ord, Read, Show)

_Datatype = (Core.Name "hydra/langs/owl/syntax.Datatype")

_Datatype_xmlSchema = (Core.Name "xmlSchema")

_Datatype_other = (Core.Name "other")

-- | See https://www.w3.org/TR/owl2-syntax/#Object_Properties
data ObjectProperty = 
  ObjectProperty {}
  deriving (Eq, Ord, Read, Show)

_ObjectProperty = (Core.Name "hydra/langs/owl/syntax.ObjectProperty")

data DataProperty = 
  DataProperty {}
  deriving (Eq, Ord, Read, Show)

_DataProperty = (Core.Name "hydra/langs/owl/syntax.DataProperty")

data AnnotationProperty = 
  AnnotationProperty {}
  deriving (Eq, Ord, Read, Show)

_AnnotationProperty = (Core.Name "hydra/langs/owl/syntax.AnnotationProperty")

data Individual = 
  IndividualNamed NamedIndividual |
  IndividualAnonymous AnonymousIndividual
  deriving (Eq, Ord, Read, Show)

_Individual = (Core.Name "hydra/langs/owl/syntax.Individual")

_Individual_named = (Core.Name "named")

_Individual_anonymous = (Core.Name "anonymous")

data NamedIndividual = 
  NamedIndividual {}
  deriving (Eq, Ord, Read, Show)

_NamedIndividual = (Core.Name "hydra/langs/owl/syntax.NamedIndividual")

data AnonymousIndividual = 
  AnonymousIndividual {}
  deriving (Eq, Ord, Read, Show)

_AnonymousIndividual = (Core.Name "hydra/langs/owl/syntax.AnonymousIndividual")

data ObjectPropertyExpression = 
  ObjectPropertyExpressionObject ObjectProperty |
  ObjectPropertyExpressionInverseObject InverseObjectProperty
  deriving (Eq, Ord, Read, Show)

_ObjectPropertyExpression = (Core.Name "hydra/langs/owl/syntax.ObjectPropertyExpression")

_ObjectPropertyExpression_object = (Core.Name "object")

_ObjectPropertyExpression_inverseObject = (Core.Name "inverseObject")

newtype InverseObjectProperty = 
  InverseObjectProperty {
    unInverseObjectProperty :: ObjectProperty}
  deriving (Eq, Ord, Read, Show)

_InverseObjectProperty = (Core.Name "hydra/langs/owl/syntax.InverseObjectProperty")

newtype DataPropertyExpression = 
  DataPropertyExpression {
    unDataPropertyExpression :: DataProperty}
  deriving (Eq, Ord, Read, Show)

_DataPropertyExpression = (Core.Name "hydra/langs/owl/syntax.DataPropertyExpression")

-- | See https://www.w3.org/TR/owl2-syntax/#Data_Ranges
data DataRange = 
  DataRangeDataComplementOf DataComplementOf |
  DataRangeDataIntersectionOf DataIntersectionOf |
  DataRangeDataOneOf DataOneOf |
  DataRangeDataUnionOf DataUnionOf |
  DataRangeDatatype Datatype |
  DataRangeDatatypeRestriction DatatypeRestriction
  deriving (Eq, Ord, Read, Show)

_DataRange = (Core.Name "hydra/langs/owl/syntax.DataRange")

_DataRange_dataComplementOf = (Core.Name "dataComplementOf")

_DataRange_dataIntersectionOf = (Core.Name "dataIntersectionOf")

_DataRange_dataOneOf = (Core.Name "dataOneOf")

_DataRange_dataUnionOf = (Core.Name "dataUnionOf")

_DataRange_datatype = (Core.Name "datatype")

_DataRange_datatypeRestriction = (Core.Name "datatypeRestriction")

-- | See https://www.w3.org/TR/owl2-syntax/#Intersection_of_Data_Ranges
newtype DataIntersectionOf = 
  DataIntersectionOf {
    -- | See https://www.w3.org/TR/owl2-syntax/#Intersection_of_Data_Ranges
    unDataIntersectionOf :: [DataRange]}
  deriving (Eq, Ord, Read, Show)

_DataIntersectionOf = (Core.Name "hydra/langs/owl/syntax.DataIntersectionOf")

-- | See https://www.w3.org/TR/owl2-syntax/#Union_of_Data_Ranges
newtype DataUnionOf = 
  DataUnionOf {
    -- | See https://www.w3.org/TR/owl2-syntax/#Union_of_Data_Ranges
    unDataUnionOf :: [DataRange]}
  deriving (Eq, Ord, Read, Show)

_DataUnionOf = (Core.Name "hydra/langs/owl/syntax.DataUnionOf")

-- | See https://www.w3.org/TR/owl2-syntax/#Complement_of_Data_Ranges
newtype DataComplementOf = 
  DataComplementOf {
    -- | See https://www.w3.org/TR/owl2-syntax/#Complement_of_Data_Ranges
    unDataComplementOf :: DataRange}
  deriving (Eq, Ord, Read, Show)

_DataComplementOf = (Core.Name "hydra/langs/owl/syntax.DataComplementOf")

-- | See https://www.w3.org/TR/owl2-syntax/#Enumeration_of_Literals
newtype DataOneOf = 
  DataOneOf {
    -- | See https://www.w3.org/TR/owl2-syntax/#Enumeration_of_Literals
    unDataOneOf :: [Syntax.Literal]}
  deriving (Eq, Ord, Read, Show)

_DataOneOf = (Core.Name "hydra/langs/owl/syntax.DataOneOf")

-- | See https://www.w3.org/TR/owl2-syntax/#Datatype_Restrictions
data DatatypeRestriction = 
  DatatypeRestriction {
    datatypeRestrictionDatatype :: Datatype,
    datatypeRestrictionConstraints :: [DatatypeRestriction_Constraint]}
  deriving (Eq, Ord, Read, Show)

_DatatypeRestriction = (Core.Name "hydra/langs/owl/syntax.DatatypeRestriction")

_DatatypeRestriction_datatype = (Core.Name "datatype")

_DatatypeRestriction_constraints = (Core.Name "constraints")

data DatatypeRestriction_Constraint = 
  DatatypeRestriction_Constraint {
    datatypeRestriction_ConstraintConstrainingFacet :: DatatypeRestriction_ConstrainingFacet,
    datatypeRestriction_ConstraintRestrictionValue :: Syntax.Literal}
  deriving (Eq, Ord, Read, Show)

_DatatypeRestriction_Constraint = (Core.Name "hydra/langs/owl/syntax.DatatypeRestriction.Constraint")

_DatatypeRestriction_Constraint_constrainingFacet = (Core.Name "constrainingFacet")

_DatatypeRestriction_Constraint_restrictionValue = (Core.Name "restrictionValue")

data DatatypeRestriction_ConstrainingFacet = 
  -- | Note: XML Schema constraining facets are treated as a special case in this model (not in the OWL 2 specification itself) because they are particularly common
  DatatypeRestriction_ConstrainingFacetXmlSchema Schema.ConstrainingFacet |
  DatatypeRestriction_ConstrainingFacetOther Syntax.Iri
  deriving (Eq, Ord, Read, Show)

_DatatypeRestriction_ConstrainingFacet = (Core.Name "hydra/langs/owl/syntax.DatatypeRestriction.ConstrainingFacet")

_DatatypeRestriction_ConstrainingFacet_xmlSchema = (Core.Name "xmlSchema")

_DatatypeRestriction_ConstrainingFacet_other = (Core.Name "other")

data ClassExpression = 
  ClassExpressionClass Class |
  ClassExpressionDataSomeValuesFrom DataSomeValuesFrom |
  ClassExpressionDataAllValuesFrom DataAllValuesFrom |
  ClassExpressionDataHasValue DataHasValue |
  ClassExpressionDataMinCardinality DataMinCardinality |
  ClassExpressionDataMaxCardinality DataMaxCardinality |
  ClassExpressionDataExactCardinality DataExactCardinality |
  ClassExpressionObjectAllValuesFrom ObjectAllValuesFrom |
  ClassExpressionObjectExactCardinality ObjectExactCardinality |
  ClassExpressionObjectHasSelf ObjectHasSelf |
  ClassExpressionObjectHasValue ObjectHasValue |
  ClassExpressionObjectIntersectionOf ObjectIntersectionOf |
  ClassExpressionObjectMaxCardinality ObjectMaxCardinality |
  ClassExpressionObjectMinCardinality ObjectMinCardinality |
  ClassExpressionObjectOneOf ObjectOneOf |
  ClassExpressionObjectSomeValuesFrom ObjectSomeValuesFrom |
  ClassExpressionObjectUnionOf ObjectUnionOf
  deriving (Eq, Ord, Read, Show)

_ClassExpression = (Core.Name "hydra/langs/owl/syntax.ClassExpression")

_ClassExpression_class = (Core.Name "class")

_ClassExpression_dataSomeValuesFrom = (Core.Name "dataSomeValuesFrom")

_ClassExpression_dataAllValuesFrom = (Core.Name "dataAllValuesFrom")

_ClassExpression_dataHasValue = (Core.Name "dataHasValue")

_ClassExpression_dataMinCardinality = (Core.Name "dataMinCardinality")

_ClassExpression_dataMaxCardinality = (Core.Name "dataMaxCardinality")

_ClassExpression_dataExactCardinality = (Core.Name "dataExactCardinality")

_ClassExpression_objectAllValuesFrom = (Core.Name "objectAllValuesFrom")

_ClassExpression_objectExactCardinality = (Core.Name "objectExactCardinality")

_ClassExpression_objectHasSelf = (Core.Name "objectHasSelf")

_ClassExpression_objectHasValue = (Core.Name "objectHasValue")

_ClassExpression_objectIntersectionOf = (Core.Name "objectIntersectionOf")

_ClassExpression_objectMaxCardinality = (Core.Name "objectMaxCardinality")

_ClassExpression_objectMinCardinality = (Core.Name "objectMinCardinality")

_ClassExpression_objectOneOf = (Core.Name "objectOneOf")

_ClassExpression_objectSomeValuesFrom = (Core.Name "objectSomeValuesFrom")

_ClassExpression_objectUnionOf = (Core.Name "objectUnionOf")

newtype ObjectIntersectionOf = 
  ObjectIntersectionOf {
    unObjectIntersectionOf :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_ObjectIntersectionOf = (Core.Name "hydra/langs/owl/syntax.ObjectIntersectionOf")

newtype ObjectUnionOf = 
  ObjectUnionOf {
    unObjectUnionOf :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_ObjectUnionOf = (Core.Name "hydra/langs/owl/syntax.ObjectUnionOf")

newtype ObjectComplementOf = 
  ObjectComplementOf {
    unObjectComplementOf :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_ObjectComplementOf = (Core.Name "hydra/langs/owl/syntax.ObjectComplementOf")

newtype ObjectOneOf = 
  ObjectOneOf {
    unObjectOneOf :: [Individual]}
  deriving (Eq, Ord, Read, Show)

_ObjectOneOf = (Core.Name "hydra/langs/owl/syntax.ObjectOneOf")

data ObjectSomeValuesFrom = 
  ObjectSomeValuesFrom {
    objectSomeValuesFromProperty :: ObjectPropertyExpression,
    objectSomeValuesFromClass :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_ObjectSomeValuesFrom = (Core.Name "hydra/langs/owl/syntax.ObjectSomeValuesFrom")

_ObjectSomeValuesFrom_property = (Core.Name "property")

_ObjectSomeValuesFrom_class = (Core.Name "class")

data ObjectAllValuesFrom = 
  ObjectAllValuesFrom {
    objectAllValuesFromProperty :: ObjectPropertyExpression,
    objectAllValuesFromClass :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_ObjectAllValuesFrom = (Core.Name "hydra/langs/owl/syntax.ObjectAllValuesFrom")

_ObjectAllValuesFrom_property = (Core.Name "property")

_ObjectAllValuesFrom_class = (Core.Name "class")

data ObjectHasValue = 
  ObjectHasValue {
    objectHasValueProperty :: ObjectPropertyExpression,
    objectHasValueIndividual :: Individual}
  deriving (Eq, Ord, Read, Show)

_ObjectHasValue = (Core.Name "hydra/langs/owl/syntax.ObjectHasValue")

_ObjectHasValue_property = (Core.Name "property")

_ObjectHasValue_individual = (Core.Name "individual")

newtype ObjectHasSelf = 
  ObjectHasSelf {
    unObjectHasSelf :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_ObjectHasSelf = (Core.Name "hydra/langs/owl/syntax.ObjectHasSelf")

-- | See https://www.w3.org/TR/owl2-syntax/#Minimum_Cardinality
data ObjectMinCardinality = 
  ObjectMinCardinality {
    objectMinCardinalityBound :: Integer,
    objectMinCardinalityProperty :: ObjectPropertyExpression,
    objectMinCardinalityClass :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_ObjectMinCardinality = (Core.Name "hydra/langs/owl/syntax.ObjectMinCardinality")

_ObjectMinCardinality_bound = (Core.Name "bound")

_ObjectMinCardinality_property = (Core.Name "property")

_ObjectMinCardinality_class = (Core.Name "class")

-- | See https://www.w3.org/TR/owl2-syntax/#Maximum_Cardinality
data ObjectMaxCardinality = 
  ObjectMaxCardinality {
    objectMaxCardinalityBound :: Integer,
    objectMaxCardinalityProperty :: ObjectPropertyExpression,
    objectMaxCardinalityClass :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_ObjectMaxCardinality = (Core.Name "hydra/langs/owl/syntax.ObjectMaxCardinality")

_ObjectMaxCardinality_bound = (Core.Name "bound")

_ObjectMaxCardinality_property = (Core.Name "property")

_ObjectMaxCardinality_class = (Core.Name "class")

-- | See https://www.w3.org/TR/owl2-syntax/#Exact_Cardinality
data ObjectExactCardinality = 
  ObjectExactCardinality {
    objectExactCardinalityBound :: Integer,
    objectExactCardinalityProperty :: ObjectPropertyExpression,
    objectExactCardinalityClass :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_ObjectExactCardinality = (Core.Name "hydra/langs/owl/syntax.ObjectExactCardinality")

_ObjectExactCardinality_bound = (Core.Name "bound")

_ObjectExactCardinality_property = (Core.Name "property")

_ObjectExactCardinality_class = (Core.Name "class")

data DataSomeValuesFrom = 
  DataSomeValuesFrom {
    dataSomeValuesFromProperty :: [DataPropertyExpression],
    dataSomeValuesFromRange :: DataRange}
  deriving (Eq, Ord, Read, Show)

_DataSomeValuesFrom = (Core.Name "hydra/langs/owl/syntax.DataSomeValuesFrom")

_DataSomeValuesFrom_property = (Core.Name "property")

_DataSomeValuesFrom_range = (Core.Name "range")

data DataAllValuesFrom = 
  DataAllValuesFrom {
    dataAllValuesFromProperty :: [DataPropertyExpression],
    dataAllValuesFromRange :: DataRange}
  deriving (Eq, Ord, Read, Show)

_DataAllValuesFrom = (Core.Name "hydra/langs/owl/syntax.DataAllValuesFrom")

_DataAllValuesFrom_property = (Core.Name "property")

_DataAllValuesFrom_range = (Core.Name "range")

data DataHasValue = 
  DataHasValue {
    dataHasValueProperty :: DataPropertyExpression,
    dataHasValueValue :: Syntax.Literal}
  deriving (Eq, Ord, Read, Show)

_DataHasValue = (Core.Name "hydra/langs/owl/syntax.DataHasValue")

_DataHasValue_property = (Core.Name "property")

_DataHasValue_value = (Core.Name "value")

data DataMinCardinality = 
  DataMinCardinality {
    dataMinCardinalityBound :: Integer,
    dataMinCardinalityProperty :: DataPropertyExpression,
    dataMinCardinalityRange :: [DataRange]}
  deriving (Eq, Ord, Read, Show)

_DataMinCardinality = (Core.Name "hydra/langs/owl/syntax.DataMinCardinality")

_DataMinCardinality_bound = (Core.Name "bound")

_DataMinCardinality_property = (Core.Name "property")

_DataMinCardinality_range = (Core.Name "range")

data DataMaxCardinality = 
  DataMaxCardinality {
    dataMaxCardinalityBound :: Integer,
    dataMaxCardinalityProperty :: DataPropertyExpression,
    dataMaxCardinalityRange :: [DataRange]}
  deriving (Eq, Ord, Read, Show)

_DataMaxCardinality = (Core.Name "hydra/langs/owl/syntax.DataMaxCardinality")

_DataMaxCardinality_bound = (Core.Name "bound")

_DataMaxCardinality_property = (Core.Name "property")

_DataMaxCardinality_range = (Core.Name "range")

data DataExactCardinality = 
  DataExactCardinality {
    dataExactCardinalityBound :: Integer,
    dataExactCardinalityProperty :: DataPropertyExpression,
    dataExactCardinalityRange :: [DataRange]}
  deriving (Eq, Ord, Read, Show)

_DataExactCardinality = (Core.Name "hydra/langs/owl/syntax.DataExactCardinality")

_DataExactCardinality_bound = (Core.Name "bound")

_DataExactCardinality_property = (Core.Name "property")

_DataExactCardinality_range = (Core.Name "range")

-- | See https://www.w3.org/TR/owl2-syntax/#Axioms
data Axiom = 
  AxiomAnnotationAxiom AnnotationAxiom |
  AxiomAssertion Assertion |
  AxiomClassAxiom ClassAxiom |
  AxiomDataPropertyAxiom DataPropertyAxiom |
  AxiomDatatypeDefinition DatatypeDefinition |
  AxiomDeclaration Declaration |
  AxiomHasKey HasKey |
  AxiomObjectPropertyAxiom ObjectPropertyAxiom
  deriving (Eq, Ord, Read, Show)

_Axiom = (Core.Name "hydra/langs/owl/syntax.Axiom")

_Axiom_annotationAxiom = (Core.Name "annotationAxiom")

_Axiom_assertion = (Core.Name "assertion")

_Axiom_classAxiom = (Core.Name "classAxiom")

_Axiom_dataPropertyAxiom = (Core.Name "dataPropertyAxiom")

_Axiom_datatypeDefinition = (Core.Name "datatypeDefinition")

_Axiom_declaration = (Core.Name "declaration")

_Axiom_hasKey = (Core.Name "hasKey")

_Axiom_objectPropertyAxiom = (Core.Name "objectPropertyAxiom")

data ClassAxiom = 
  ClassAxiomDisjointClasses DisjointClasses |
  ClassAxiomDisjointUnion DisjointUnion |
  ClassAxiomEquivalentClasses EquivalentClasses |
  ClassAxiomSubClassOf SubClassOf
  deriving (Eq, Ord, Read, Show)

_ClassAxiom = (Core.Name "hydra/langs/owl/syntax.ClassAxiom")

_ClassAxiom_disjointClasses = (Core.Name "disjointClasses")

_ClassAxiom_disjointUnion = (Core.Name "disjointUnion")

_ClassAxiom_equivalentClasses = (Core.Name "equivalentClasses")

_ClassAxiom_subClassOf = (Core.Name "subClassOf")

data SubClassOf = 
  SubClassOf {
    subClassOfAnnotations :: [Annotation],
    subClassOfSubClass :: ClassExpression,
    subClassOfSuperClass :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_SubClassOf = (Core.Name "hydra/langs/owl/syntax.SubClassOf")

_SubClassOf_annotations = (Core.Name "annotations")

_SubClassOf_subClass = (Core.Name "subClass")

_SubClassOf_superClass = (Core.Name "superClass")

data EquivalentClasses = 
  EquivalentClasses {
    equivalentClassesAnnotations :: [Annotation],
    equivalentClassesClasses :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_EquivalentClasses = (Core.Name "hydra/langs/owl/syntax.EquivalentClasses")

_EquivalentClasses_annotations = (Core.Name "annotations")

_EquivalentClasses_classes = (Core.Name "classes")

data DisjointClasses = 
  DisjointClasses {
    disjointClassesAnnotations :: [Annotation],
    disjointClassesClasses :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_DisjointClasses = (Core.Name "hydra/langs/owl/syntax.DisjointClasses")

_DisjointClasses_annotations = (Core.Name "annotations")

_DisjointClasses_classes = (Core.Name "classes")

-- | See https://www.w3.org/TR/owl2-syntax/#Disjoint_Union_of_Class_Expressions
data DisjointUnion = 
  DisjointUnion {
    disjointUnionAnnotations :: [Annotation],
    disjointUnionClass :: Class,
    disjointUnionClasses :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_DisjointUnion = (Core.Name "hydra/langs/owl/syntax.DisjointUnion")

_DisjointUnion_annotations = (Core.Name "annotations")

_DisjointUnion_class = (Core.Name "class")

_DisjointUnion_classes = (Core.Name "classes")

data ObjectPropertyAxiom = 
  ObjectPropertyAxiomAsymmetricObjectProperty AsymmetricObjectProperty |
  ObjectPropertyAxiomDisjointObjectProperties DisjointObjectProperties |
  ObjectPropertyAxiomEquivalentObjectProperties EquivalentObjectProperties |
  ObjectPropertyAxiomFunctionalObjectProperty FunctionalObjectProperty |
  ObjectPropertyAxiomInverseFunctionalObjectProperty InverseFunctionalObjectProperty |
  ObjectPropertyAxiomInverseObjectProperties InverseObjectProperties |
  ObjectPropertyAxiomIrreflexiveObjectProperty IrreflexiveObjectProperty |
  ObjectPropertyAxiomObjectPropertyDomain ObjectPropertyDomain |
  ObjectPropertyAxiomObjectPropertyRange ObjectPropertyRange |
  ObjectPropertyAxiomReflexiveObjectProperty ReflexiveObjectProperty |
  ObjectPropertyAxiomSubObjectPropertyOf SubObjectPropertyOf |
  ObjectPropertyAxiomSymmetricObjectProperty SymmetricObjectProperty |
  ObjectPropertyAxiomTransitiveObjectProperty TransitiveObjectProperty
  deriving (Eq, Ord, Read, Show)

_ObjectPropertyAxiom = (Core.Name "hydra/langs/owl/syntax.ObjectPropertyAxiom")

_ObjectPropertyAxiom_asymmetricObjectProperty = (Core.Name "asymmetricObjectProperty")

_ObjectPropertyAxiom_disjointObjectProperties = (Core.Name "disjointObjectProperties")

_ObjectPropertyAxiom_equivalentObjectProperties = (Core.Name "equivalentObjectProperties")

_ObjectPropertyAxiom_functionalObjectProperty = (Core.Name "functionalObjectProperty")

_ObjectPropertyAxiom_inverseFunctionalObjectProperty = (Core.Name "inverseFunctionalObjectProperty")

_ObjectPropertyAxiom_inverseObjectProperties = (Core.Name "inverseObjectProperties")

_ObjectPropertyAxiom_irreflexiveObjectProperty = (Core.Name "irreflexiveObjectProperty")

_ObjectPropertyAxiom_objectPropertyDomain = (Core.Name "objectPropertyDomain")

_ObjectPropertyAxiom_objectPropertyRange = (Core.Name "objectPropertyRange")

_ObjectPropertyAxiom_reflexiveObjectProperty = (Core.Name "reflexiveObjectProperty")

_ObjectPropertyAxiom_subObjectPropertyOf = (Core.Name "subObjectPropertyOf")

_ObjectPropertyAxiom_symmetricObjectProperty = (Core.Name "symmetricObjectProperty")

_ObjectPropertyAxiom_transitiveObjectProperty = (Core.Name "transitiveObjectProperty")

data SubObjectPropertyOf = 
  SubObjectPropertyOf {
    subObjectPropertyOfAnnotations :: [Annotation],
    subObjectPropertyOfSubProperty :: [ObjectPropertyExpression],
    subObjectPropertyOfSuperProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_SubObjectPropertyOf = (Core.Name "hydra/langs/owl/syntax.SubObjectPropertyOf")

_SubObjectPropertyOf_annotations = (Core.Name "annotations")

_SubObjectPropertyOf_subProperty = (Core.Name "subProperty")

_SubObjectPropertyOf_superProperty = (Core.Name "superProperty")

data EquivalentObjectProperties = 
  EquivalentObjectProperties {
    equivalentObjectPropertiesAnnotations :: [Annotation],
    equivalentObjectPropertiesProperties :: [ObjectPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_EquivalentObjectProperties = (Core.Name "hydra/langs/owl/syntax.EquivalentObjectProperties")

_EquivalentObjectProperties_annotations = (Core.Name "annotations")

_EquivalentObjectProperties_properties = (Core.Name "properties")

data DisjointObjectProperties = 
  DisjointObjectProperties {
    disjointObjectPropertiesAnnotations :: [Annotation],
    disjointObjectPropertiesProperties :: [ObjectPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_DisjointObjectProperties = (Core.Name "hydra/langs/owl/syntax.DisjointObjectProperties")

_DisjointObjectProperties_annotations = (Core.Name "annotations")

_DisjointObjectProperties_properties = (Core.Name "properties")

-- | See https://www.w3.org/TR/owl2-syntax/#Object_Property_Domain
data ObjectPropertyDomain = 
  ObjectPropertyDomain {
    objectPropertyDomainAnnotations :: [Annotation],
    objectPropertyDomainProperty :: ObjectPropertyExpression,
    objectPropertyDomainDomain :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_ObjectPropertyDomain = (Core.Name "hydra/langs/owl/syntax.ObjectPropertyDomain")

_ObjectPropertyDomain_annotations = (Core.Name "annotations")

_ObjectPropertyDomain_property = (Core.Name "property")

_ObjectPropertyDomain_domain = (Core.Name "domain")

-- | See https://www.w3.org/TR/owl2-syntax/#Object_Property_Range
data ObjectPropertyRange = 
  ObjectPropertyRange {
    objectPropertyRangeAnnotations :: [Annotation],
    objectPropertyRangeProperty :: ObjectPropertyExpression,
    objectPropertyRangeRange :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_ObjectPropertyRange = (Core.Name "hydra/langs/owl/syntax.ObjectPropertyRange")

_ObjectPropertyRange_annotations = (Core.Name "annotations")

_ObjectPropertyRange_property = (Core.Name "property")

_ObjectPropertyRange_range = (Core.Name "range")

data InverseObjectProperties = 
  InverseObjectProperties {
    inverseObjectPropertiesAnnotations :: [Annotation],
    inverseObjectPropertiesProperty1 :: ObjectPropertyExpression,
    inverseObjectPropertiesProperty2 :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_InverseObjectProperties = (Core.Name "hydra/langs/owl/syntax.InverseObjectProperties")

_InverseObjectProperties_annotations = (Core.Name "annotations")

_InverseObjectProperties_property1 = (Core.Name "property1")

_InverseObjectProperties_property2 = (Core.Name "property2")

data FunctionalObjectProperty = 
  FunctionalObjectProperty {
    functionalObjectPropertyAnnotations :: [Annotation],
    functionalObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_FunctionalObjectProperty = (Core.Name "hydra/langs/owl/syntax.FunctionalObjectProperty")

_FunctionalObjectProperty_annotations = (Core.Name "annotations")

_FunctionalObjectProperty_property = (Core.Name "property")

data InverseFunctionalObjectProperty = 
  InverseFunctionalObjectProperty {
    inverseFunctionalObjectPropertyAnnotations :: [Annotation],
    inverseFunctionalObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_InverseFunctionalObjectProperty = (Core.Name "hydra/langs/owl/syntax.InverseFunctionalObjectProperty")

_InverseFunctionalObjectProperty_annotations = (Core.Name "annotations")

_InverseFunctionalObjectProperty_property = (Core.Name "property")

data ReflexiveObjectProperty = 
  ReflexiveObjectProperty {
    reflexiveObjectPropertyAnnotations :: [Annotation],
    reflexiveObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_ReflexiveObjectProperty = (Core.Name "hydra/langs/owl/syntax.ReflexiveObjectProperty")

_ReflexiveObjectProperty_annotations = (Core.Name "annotations")

_ReflexiveObjectProperty_property = (Core.Name "property")

data IrreflexiveObjectProperty = 
  IrreflexiveObjectProperty {
    irreflexiveObjectPropertyAnnotations :: [Annotation],
    irreflexiveObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_IrreflexiveObjectProperty = (Core.Name "hydra/langs/owl/syntax.IrreflexiveObjectProperty")

_IrreflexiveObjectProperty_annotations = (Core.Name "annotations")

_IrreflexiveObjectProperty_property = (Core.Name "property")

data SymmetricObjectProperty = 
  SymmetricObjectProperty {
    symmetricObjectPropertyAnnotations :: [Annotation],
    symmetricObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_SymmetricObjectProperty = (Core.Name "hydra/langs/owl/syntax.SymmetricObjectProperty")

_SymmetricObjectProperty_annotations = (Core.Name "annotations")

_SymmetricObjectProperty_property = (Core.Name "property")

data AsymmetricObjectProperty = 
  AsymmetricObjectProperty {
    asymmetricObjectPropertyAnnotations :: [Annotation],
    asymmetricObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_AsymmetricObjectProperty = (Core.Name "hydra/langs/owl/syntax.AsymmetricObjectProperty")

_AsymmetricObjectProperty_annotations = (Core.Name "annotations")

_AsymmetricObjectProperty_property = (Core.Name "property")

data TransitiveObjectProperty = 
  TransitiveObjectProperty {
    transitiveObjectPropertyAnnotations :: [Annotation],
    transitiveObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_TransitiveObjectProperty = (Core.Name "hydra/langs/owl/syntax.TransitiveObjectProperty")

_TransitiveObjectProperty_annotations = (Core.Name "annotations")

_TransitiveObjectProperty_property = (Core.Name "property")

data DataPropertyAxiom = 
  DataPropertyAxiomDataPropertyAxiom DataPropertyAxiom |
  DataPropertyAxiomDataPropertyRange DataPropertyRange |
  DataPropertyAxiomDisjointDataProperties DisjointDataProperties |
  DataPropertyAxiomEquivalentDataProperties EquivalentDataProperties |
  DataPropertyAxiomFunctionalDataProperty FunctionalDataProperty |
  DataPropertyAxiomSubDataPropertyOf SubDataPropertyOf
  deriving (Eq, Ord, Read, Show)

_DataPropertyAxiom = (Core.Name "hydra/langs/owl/syntax.DataPropertyAxiom")

_DataPropertyAxiom_dataPropertyAxiom = (Core.Name "dataPropertyAxiom")

_DataPropertyAxiom_dataPropertyRange = (Core.Name "dataPropertyRange")

_DataPropertyAxiom_disjointDataProperties = (Core.Name "disjointDataProperties")

_DataPropertyAxiom_equivalentDataProperties = (Core.Name "equivalentDataProperties")

_DataPropertyAxiom_functionalDataProperty = (Core.Name "functionalDataProperty")

_DataPropertyAxiom_subDataPropertyOf = (Core.Name "subDataPropertyOf")

data SubDataPropertyOf = 
  SubDataPropertyOf {
    subDataPropertyOfAnnotations :: [Annotation],
    subDataPropertyOfSubProperty :: DataPropertyExpression,
    subDataPropertyOfSuperProperty :: DataPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_SubDataPropertyOf = (Core.Name "hydra/langs/owl/syntax.SubDataPropertyOf")

_SubDataPropertyOf_annotations = (Core.Name "annotations")

_SubDataPropertyOf_subProperty = (Core.Name "subProperty")

_SubDataPropertyOf_superProperty = (Core.Name "superProperty")

data EquivalentDataProperties = 
  EquivalentDataProperties {
    equivalentDataPropertiesAnnotations :: [Annotation],
    equivalentDataPropertiesProperties :: [DataPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_EquivalentDataProperties = (Core.Name "hydra/langs/owl/syntax.EquivalentDataProperties")

_EquivalentDataProperties_annotations = (Core.Name "annotations")

_EquivalentDataProperties_properties = (Core.Name "properties")

data DisjointDataProperties = 
  DisjointDataProperties {
    disjointDataPropertiesAnnotations :: [Annotation],
    disjointDataPropertiesProperties :: [DataPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_DisjointDataProperties = (Core.Name "hydra/langs/owl/syntax.DisjointDataProperties")

_DisjointDataProperties_annotations = (Core.Name "annotations")

_DisjointDataProperties_properties = (Core.Name "properties")

data DataPropertyDomain = 
  DataPropertyDomain {
    dataPropertyDomainAnnotations :: [Annotation],
    dataPropertyDomainProperty :: DataPropertyExpression,
    dataPropertyDomainDomain :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_DataPropertyDomain = (Core.Name "hydra/langs/owl/syntax.DataPropertyDomain")

_DataPropertyDomain_annotations = (Core.Name "annotations")

_DataPropertyDomain_property = (Core.Name "property")

_DataPropertyDomain_domain = (Core.Name "domain")

data DataPropertyRange = 
  DataPropertyRange {
    dataPropertyRangeAnnotations :: [Annotation],
    dataPropertyRangeProperty :: DataPropertyExpression,
    dataPropertyRangeRange :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_DataPropertyRange = (Core.Name "hydra/langs/owl/syntax.DataPropertyRange")

_DataPropertyRange_annotations = (Core.Name "annotations")

_DataPropertyRange_property = (Core.Name "property")

_DataPropertyRange_range = (Core.Name "range")

data FunctionalDataProperty = 
  FunctionalDataProperty {
    functionalDataPropertyAnnotations :: [Annotation],
    functionalDataPropertyProperty :: DataPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_FunctionalDataProperty = (Core.Name "hydra/langs/owl/syntax.FunctionalDataProperty")

_FunctionalDataProperty_annotations = (Core.Name "annotations")

_FunctionalDataProperty_property = (Core.Name "property")

data DatatypeDefinition = 
  DatatypeDefinition {
    datatypeDefinitionAnnotations :: [Annotation],
    datatypeDefinitionDatatype :: Datatype,
    datatypeDefinitionRange :: DataRange}
  deriving (Eq, Ord, Read, Show)

_DatatypeDefinition = (Core.Name "hydra/langs/owl/syntax.DatatypeDefinition")

_DatatypeDefinition_annotations = (Core.Name "annotations")

_DatatypeDefinition_datatype = (Core.Name "datatype")

_DatatypeDefinition_range = (Core.Name "range")

-- | See https://www.w3.org/TR/owl2-syntax/#Keys
data HasKey = 
  HasKey {
    hasKeyAnnotations :: [Annotation],
    hasKeyClass :: ClassExpression,
    hasKeyObjectProperties :: [ObjectPropertyExpression],
    hasKeyDataProperties :: [DataPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_HasKey = (Core.Name "hydra/langs/owl/syntax.HasKey")

_HasKey_annotations = (Core.Name "annotations")

_HasKey_class = (Core.Name "class")

_HasKey_objectProperties = (Core.Name "objectProperties")

_HasKey_dataProperties = (Core.Name "dataProperties")

data Assertion = 
  AssertionClassAssertion ClassAssertion |
  AssertionDataPropertyAssertion DataPropertyAssertion |
  AssertionDifferentIndividuals DifferentIndividuals |
  AssertionObjectPropertyAssertion ObjectPropertyAssertion |
  AssertionNegativeDataPropertyAssertion NegativeDataPropertyAssertion |
  AssertionNegativeObjectPropertyAssertion NegativeObjectPropertyAssertion |
  AssertionSameIndividual SameIndividual
  deriving (Eq, Ord, Read, Show)

_Assertion = (Core.Name "hydra/langs/owl/syntax.Assertion")

_Assertion_classAssertion = (Core.Name "classAssertion")

_Assertion_dataPropertyAssertion = (Core.Name "dataPropertyAssertion")

_Assertion_differentIndividuals = (Core.Name "differentIndividuals")

_Assertion_objectPropertyAssertion = (Core.Name "objectPropertyAssertion")

_Assertion_negativeDataPropertyAssertion = (Core.Name "negativeDataPropertyAssertion")

_Assertion_negativeObjectPropertyAssertion = (Core.Name "negativeObjectPropertyAssertion")

_Assertion_sameIndividual = (Core.Name "sameIndividual")

data SameIndividual = 
  SameIndividual {
    sameIndividualAnnotations :: [Annotation],
    sameIndividualIndividuals :: [Individual]}
  deriving (Eq, Ord, Read, Show)

_SameIndividual = (Core.Name "hydra/langs/owl/syntax.SameIndividual")

_SameIndividual_annotations = (Core.Name "annotations")

_SameIndividual_individuals = (Core.Name "individuals")

data DifferentIndividuals = 
  DifferentIndividuals {
    differentIndividualsAnnotations :: [Annotation],
    differentIndividualsIndividuals :: [Individual]}
  deriving (Eq, Ord, Read, Show)

_DifferentIndividuals = (Core.Name "hydra/langs/owl/syntax.DifferentIndividuals")

_DifferentIndividuals_annotations = (Core.Name "annotations")

_DifferentIndividuals_individuals = (Core.Name "individuals")

data ClassAssertion = 
  ClassAssertion {
    classAssertionAnnotations :: [Annotation],
    classAssertionClass :: ClassExpression,
    classAssertionIndividual :: Individual}
  deriving (Eq, Ord, Read, Show)

_ClassAssertion = (Core.Name "hydra/langs/owl/syntax.ClassAssertion")

_ClassAssertion_annotations = (Core.Name "annotations")

_ClassAssertion_class = (Core.Name "class")

_ClassAssertion_individual = (Core.Name "individual")

data ObjectPropertyAssertion = 
  ObjectPropertyAssertion {
    objectPropertyAssertionAnnotations :: [Annotation],
    objectPropertyAssertionProperty :: ObjectPropertyExpression,
    objectPropertyAssertionSource :: Individual,
    objectPropertyAssertionTarget :: Individual}
  deriving (Eq, Ord, Read, Show)

_ObjectPropertyAssertion = (Core.Name "hydra/langs/owl/syntax.ObjectPropertyAssertion")

_ObjectPropertyAssertion_annotations = (Core.Name "annotations")

_ObjectPropertyAssertion_property = (Core.Name "property")

_ObjectPropertyAssertion_source = (Core.Name "source")

_ObjectPropertyAssertion_target = (Core.Name "target")

data NegativeObjectPropertyAssertion = 
  NegativeObjectPropertyAssertion {
    negativeObjectPropertyAssertionAnnotations :: [Annotation],
    negativeObjectPropertyAssertionProperty :: ObjectPropertyExpression,
    negativeObjectPropertyAssertionSource :: Individual,
    negativeObjectPropertyAssertionTarget :: Individual}
  deriving (Eq, Ord, Read, Show)

_NegativeObjectPropertyAssertion = (Core.Name "hydra/langs/owl/syntax.NegativeObjectPropertyAssertion")

_NegativeObjectPropertyAssertion_annotations = (Core.Name "annotations")

_NegativeObjectPropertyAssertion_property = (Core.Name "property")

_NegativeObjectPropertyAssertion_source = (Core.Name "source")

_NegativeObjectPropertyAssertion_target = (Core.Name "target")

data DataPropertyAssertion = 
  DataPropertyAssertion {
    dataPropertyAssertionAnnotations :: [Annotation],
    dataPropertyAssertionProperty :: DataPropertyExpression,
    dataPropertyAssertionSource :: Individual,
    dataPropertyAssertionTarget :: Individual}
  deriving (Eq, Ord, Read, Show)

_DataPropertyAssertion = (Core.Name "hydra/langs/owl/syntax.DataPropertyAssertion")

_DataPropertyAssertion_annotations = (Core.Name "annotations")

_DataPropertyAssertion_property = (Core.Name "property")

_DataPropertyAssertion_source = (Core.Name "source")

_DataPropertyAssertion_target = (Core.Name "target")

data NegativeDataPropertyAssertion = 
  NegativeDataPropertyAssertion {
    negativeDataPropertyAssertionAnnotations :: [Annotation],
    negativeDataPropertyAssertionProperty :: DataPropertyExpression,
    negativeDataPropertyAssertionSource :: Individual,
    negativeDataPropertyAssertionTarget :: Individual}
  deriving (Eq, Ord, Read, Show)

_NegativeDataPropertyAssertion = (Core.Name "hydra/langs/owl/syntax.NegativeDataPropertyAssertion")

_NegativeDataPropertyAssertion_annotations = (Core.Name "annotations")

_NegativeDataPropertyAssertion_property = (Core.Name "property")

_NegativeDataPropertyAssertion_source = (Core.Name "source")

_NegativeDataPropertyAssertion_target = (Core.Name "target")
