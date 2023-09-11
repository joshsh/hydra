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

_Ontology_directImports = (Core.FieldName "directImports")

_Ontology_annotations = (Core.FieldName "annotations")

_Ontology_axioms = (Core.FieldName "axioms")

data Declaration = 
  Declaration {
    declarationAnnotations :: [Annotation],
    declarationEntity :: Entity}
  deriving (Eq, Ord, Read, Show)

_Declaration = (Core.Name "hydra/langs/owl/syntax.Declaration")

_Declaration_annotations = (Core.FieldName "annotations")

_Declaration_entity = (Core.FieldName "entity")

data Entity = 
  EntityAnnotationProperty AnnotationProperty |
  EntityClass Class |
  EntityDataProperty DataProperty |
  EntityDatatype Datatype |
  EntityNamedIndividual NamedIndividual |
  EntityObjectProperty ObjectProperty
  deriving (Eq, Ord, Read, Show)

_Entity = (Core.Name "hydra/langs/owl/syntax.Entity")

_Entity_annotationProperty = (Core.FieldName "annotationProperty")

_Entity_class = (Core.FieldName "class")

_Entity_dataProperty = (Core.FieldName "dataProperty")

_Entity_datatype = (Core.FieldName "datatype")

_Entity_namedIndividual = (Core.FieldName "namedIndividual")

_Entity_objectProperty = (Core.FieldName "objectProperty")

data AnnotationSubject = 
  AnnotationSubjectIri Syntax.Iri |
  AnnotationSubjectAnonymousIndividual AnonymousIndividual
  deriving (Eq, Ord, Read, Show)

_AnnotationSubject = (Core.Name "hydra/langs/owl/syntax.AnnotationSubject")

_AnnotationSubject_iri = (Core.FieldName "iri")

_AnnotationSubject_anonymousIndividual = (Core.FieldName "anonymousIndividual")

data AnnotationValue = 
  AnnotationValueAnonymousIndividual AnonymousIndividual |
  AnnotationValueIri Syntax.Iri |
  AnnotationValueLiteral Syntax.Literal
  deriving (Eq, Ord, Read, Show)

_AnnotationValue = (Core.Name "hydra/langs/owl/syntax.AnnotationValue")

_AnnotationValue_anonymousIndividual = (Core.FieldName "anonymousIndividual")

_AnnotationValue_iri = (Core.FieldName "iri")

_AnnotationValue_literal = (Core.FieldName "literal")

data Annotation = 
  Annotation {
    annotationAnnotations :: [Annotation],
    annotationProperty :: AnnotationProperty,
    annotationValue :: AnnotationValue}
  deriving (Eq, Ord, Read, Show)

_Annotation = (Core.Name "hydra/langs/owl/syntax.Annotation")

_Annotation_annotations = (Core.FieldName "annotations")

_Annotation_property = (Core.FieldName "property")

_Annotation_value = (Core.FieldName "value")

data AnnotationAxiom = 
  AnnotationAxiomAnnotationAssertion AnnotationAssertion |
  AnnotationAxiomAnnotationPropertyDomain AnnotationPropertyDomain |
  AnnotationAxiomAnnotationPropertyRange AnnotationPropertyRange |
  AnnotationAxiomSubAnnotationPropertyOf SubAnnotationPropertyOf
  deriving (Eq, Ord, Read, Show)

_AnnotationAxiom = (Core.Name "hydra/langs/owl/syntax.AnnotationAxiom")

_AnnotationAxiom_annotationAssertion = (Core.FieldName "annotationAssertion")

_AnnotationAxiom_annotationPropertyDomain = (Core.FieldName "annotationPropertyDomain")

_AnnotationAxiom_annotationPropertyRange = (Core.FieldName "annotationPropertyRange")

_AnnotationAxiom_subAnnotationPropertyOf = (Core.FieldName "subAnnotationPropertyOf")

data AnnotationAssertion = 
  AnnotationAssertion {
    annotationAssertionAnnotations :: [Annotation],
    annotationAssertionProperty :: AnnotationProperty,
    annotationAssertionSubject :: AnnotationSubject,
    annotationAssertionValue :: AnnotationValue}
  deriving (Eq, Ord, Read, Show)

_AnnotationAssertion = (Core.Name "hydra/langs/owl/syntax.AnnotationAssertion")

_AnnotationAssertion_annotations = (Core.FieldName "annotations")

_AnnotationAssertion_property = (Core.FieldName "property")

_AnnotationAssertion_subject = (Core.FieldName "subject")

_AnnotationAssertion_value = (Core.FieldName "value")

data SubAnnotationPropertyOf = 
  SubAnnotationPropertyOf {
    subAnnotationPropertyOfAnnotations :: [Annotation],
    subAnnotationPropertyOfSubProperty :: AnnotationProperty,
    subAnnotationPropertyOfSuperProperty :: AnnotationProperty}
  deriving (Eq, Ord, Read, Show)

_SubAnnotationPropertyOf = (Core.Name "hydra/langs/owl/syntax.SubAnnotationPropertyOf")

_SubAnnotationPropertyOf_annotations = (Core.FieldName "annotations")

_SubAnnotationPropertyOf_subProperty = (Core.FieldName "subProperty")

_SubAnnotationPropertyOf_superProperty = (Core.FieldName "superProperty")

data AnnotationPropertyDomain = 
  AnnotationPropertyDomain {
    annotationPropertyDomainAnnotations :: [Annotation],
    annotationPropertyDomainProperty :: AnnotationProperty,
    annotationPropertyDomainIri :: Syntax.Iri}
  deriving (Eq, Ord, Read, Show)

_AnnotationPropertyDomain = (Core.Name "hydra/langs/owl/syntax.AnnotationPropertyDomain")

_AnnotationPropertyDomain_annotations = (Core.FieldName "annotations")

_AnnotationPropertyDomain_property = (Core.FieldName "property")

_AnnotationPropertyDomain_iri = (Core.FieldName "iri")

data AnnotationPropertyRange = 
  AnnotationPropertyRange {
    annotationPropertyRangeAnnotations :: [Annotation],
    annotationPropertyRangeProperty :: AnnotationProperty,
    annotationPropertyRangeIri :: Syntax.Iri}
  deriving (Eq, Ord, Read, Show)

_AnnotationPropertyRange = (Core.Name "hydra/langs/owl/syntax.AnnotationPropertyRange")

_AnnotationPropertyRange_annotations = (Core.FieldName "annotations")

_AnnotationPropertyRange_property = (Core.FieldName "property")

_AnnotationPropertyRange_iri = (Core.FieldName "iri")

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

_Datatype_xmlSchema = (Core.FieldName "xmlSchema")

_Datatype_other = (Core.FieldName "other")

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

_Individual_named = (Core.FieldName "named")

_Individual_anonymous = (Core.FieldName "anonymous")

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

_ObjectPropertyExpression_object = (Core.FieldName "object")

_ObjectPropertyExpression_inverseObject = (Core.FieldName "inverseObject")

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

_DataRange_dataComplementOf = (Core.FieldName "dataComplementOf")

_DataRange_dataIntersectionOf = (Core.FieldName "dataIntersectionOf")

_DataRange_dataOneOf = (Core.FieldName "dataOneOf")

_DataRange_dataUnionOf = (Core.FieldName "dataUnionOf")

_DataRange_datatype = (Core.FieldName "datatype")

_DataRange_datatypeRestriction = (Core.FieldName "datatypeRestriction")

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

_DatatypeRestriction_datatype = (Core.FieldName "datatype")

_DatatypeRestriction_constraints = (Core.FieldName "constraints")

data DatatypeRestriction_Constraint = 
  DatatypeRestriction_Constraint {
    datatypeRestriction_ConstraintConstrainingFacet :: DatatypeRestriction_ConstrainingFacet,
    datatypeRestriction_ConstraintRestrictionValue :: Syntax.Literal}
  deriving (Eq, Ord, Read, Show)

_DatatypeRestriction_Constraint = (Core.Name "hydra/langs/owl/syntax.DatatypeRestriction.Constraint")

_DatatypeRestriction_Constraint_constrainingFacet = (Core.FieldName "constrainingFacet")

_DatatypeRestriction_Constraint_restrictionValue = (Core.FieldName "restrictionValue")

data DatatypeRestriction_ConstrainingFacet = 
  -- | Note: XML Schema constraining facets are treated as a special case in this model (not in the OWL 2 specification itself) because they are particularly common
  DatatypeRestriction_ConstrainingFacetXmlSchema Schema.ConstrainingFacet |
  DatatypeRestriction_ConstrainingFacetOther Syntax.Iri
  deriving (Eq, Ord, Read, Show)

_DatatypeRestriction_ConstrainingFacet = (Core.Name "hydra/langs/owl/syntax.DatatypeRestriction.ConstrainingFacet")

_DatatypeRestriction_ConstrainingFacet_xmlSchema = (Core.FieldName "xmlSchema")

_DatatypeRestriction_ConstrainingFacet_other = (Core.FieldName "other")

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

_ClassExpression_class = (Core.FieldName "class")

_ClassExpression_dataSomeValuesFrom = (Core.FieldName "dataSomeValuesFrom")

_ClassExpression_dataAllValuesFrom = (Core.FieldName "dataAllValuesFrom")

_ClassExpression_dataHasValue = (Core.FieldName "dataHasValue")

_ClassExpression_dataMinCardinality = (Core.FieldName "dataMinCardinality")

_ClassExpression_dataMaxCardinality = (Core.FieldName "dataMaxCardinality")

_ClassExpression_dataExactCardinality = (Core.FieldName "dataExactCardinality")

_ClassExpression_objectAllValuesFrom = (Core.FieldName "objectAllValuesFrom")

_ClassExpression_objectExactCardinality = (Core.FieldName "objectExactCardinality")

_ClassExpression_objectHasSelf = (Core.FieldName "objectHasSelf")

_ClassExpression_objectHasValue = (Core.FieldName "objectHasValue")

_ClassExpression_objectIntersectionOf = (Core.FieldName "objectIntersectionOf")

_ClassExpression_objectMaxCardinality = (Core.FieldName "objectMaxCardinality")

_ClassExpression_objectMinCardinality = (Core.FieldName "objectMinCardinality")

_ClassExpression_objectOneOf = (Core.FieldName "objectOneOf")

_ClassExpression_objectSomeValuesFrom = (Core.FieldName "objectSomeValuesFrom")

_ClassExpression_objectUnionOf = (Core.FieldName "objectUnionOf")

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

_ObjectSomeValuesFrom_property = (Core.FieldName "property")

_ObjectSomeValuesFrom_class = (Core.FieldName "class")

data ObjectAllValuesFrom = 
  ObjectAllValuesFrom {
    objectAllValuesFromProperty :: ObjectPropertyExpression,
    objectAllValuesFromClass :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_ObjectAllValuesFrom = (Core.Name "hydra/langs/owl/syntax.ObjectAllValuesFrom")

_ObjectAllValuesFrom_property = (Core.FieldName "property")

_ObjectAllValuesFrom_class = (Core.FieldName "class")

data ObjectHasValue = 
  ObjectHasValue {
    objectHasValueProperty :: ObjectPropertyExpression,
    objectHasValueIndividual :: Individual}
  deriving (Eq, Ord, Read, Show)

_ObjectHasValue = (Core.Name "hydra/langs/owl/syntax.ObjectHasValue")

_ObjectHasValue_property = (Core.FieldName "property")

_ObjectHasValue_individual = (Core.FieldName "individual")

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

_ObjectMinCardinality_bound = (Core.FieldName "bound")

_ObjectMinCardinality_property = (Core.FieldName "property")

_ObjectMinCardinality_class = (Core.FieldName "class")

-- | See https://www.w3.org/TR/owl2-syntax/#Maximum_Cardinality
data ObjectMaxCardinality = 
  ObjectMaxCardinality {
    objectMaxCardinalityBound :: Integer,
    objectMaxCardinalityProperty :: ObjectPropertyExpression,
    objectMaxCardinalityClass :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_ObjectMaxCardinality = (Core.Name "hydra/langs/owl/syntax.ObjectMaxCardinality")

_ObjectMaxCardinality_bound = (Core.FieldName "bound")

_ObjectMaxCardinality_property = (Core.FieldName "property")

_ObjectMaxCardinality_class = (Core.FieldName "class")

-- | See https://www.w3.org/TR/owl2-syntax/#Exact_Cardinality
data ObjectExactCardinality = 
  ObjectExactCardinality {
    objectExactCardinalityBound :: Integer,
    objectExactCardinalityProperty :: ObjectPropertyExpression,
    objectExactCardinalityClass :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_ObjectExactCardinality = (Core.Name "hydra/langs/owl/syntax.ObjectExactCardinality")

_ObjectExactCardinality_bound = (Core.FieldName "bound")

_ObjectExactCardinality_property = (Core.FieldName "property")

_ObjectExactCardinality_class = (Core.FieldName "class")

data DataSomeValuesFrom = 
  DataSomeValuesFrom {
    dataSomeValuesFromProperty :: [DataPropertyExpression],
    dataSomeValuesFromRange :: DataRange}
  deriving (Eq, Ord, Read, Show)

_DataSomeValuesFrom = (Core.Name "hydra/langs/owl/syntax.DataSomeValuesFrom")

_DataSomeValuesFrom_property = (Core.FieldName "property")

_DataSomeValuesFrom_range = (Core.FieldName "range")

data DataAllValuesFrom = 
  DataAllValuesFrom {
    dataAllValuesFromProperty :: [DataPropertyExpression],
    dataAllValuesFromRange :: DataRange}
  deriving (Eq, Ord, Read, Show)

_DataAllValuesFrom = (Core.Name "hydra/langs/owl/syntax.DataAllValuesFrom")

_DataAllValuesFrom_property = (Core.FieldName "property")

_DataAllValuesFrom_range = (Core.FieldName "range")

data DataHasValue = 
  DataHasValue {
    dataHasValueProperty :: DataPropertyExpression,
    dataHasValueValue :: Syntax.Literal}
  deriving (Eq, Ord, Read, Show)

_DataHasValue = (Core.Name "hydra/langs/owl/syntax.DataHasValue")

_DataHasValue_property = (Core.FieldName "property")

_DataHasValue_value = (Core.FieldName "value")

data DataMinCardinality = 
  DataMinCardinality {
    dataMinCardinalityBound :: Integer,
    dataMinCardinalityProperty :: DataPropertyExpression,
    dataMinCardinalityRange :: [DataRange]}
  deriving (Eq, Ord, Read, Show)

_DataMinCardinality = (Core.Name "hydra/langs/owl/syntax.DataMinCardinality")

_DataMinCardinality_bound = (Core.FieldName "bound")

_DataMinCardinality_property = (Core.FieldName "property")

_DataMinCardinality_range = (Core.FieldName "range")

data DataMaxCardinality = 
  DataMaxCardinality {
    dataMaxCardinalityBound :: Integer,
    dataMaxCardinalityProperty :: DataPropertyExpression,
    dataMaxCardinalityRange :: [DataRange]}
  deriving (Eq, Ord, Read, Show)

_DataMaxCardinality = (Core.Name "hydra/langs/owl/syntax.DataMaxCardinality")

_DataMaxCardinality_bound = (Core.FieldName "bound")

_DataMaxCardinality_property = (Core.FieldName "property")

_DataMaxCardinality_range = (Core.FieldName "range")

data DataExactCardinality = 
  DataExactCardinality {
    dataExactCardinalityBound :: Integer,
    dataExactCardinalityProperty :: DataPropertyExpression,
    dataExactCardinalityRange :: [DataRange]}
  deriving (Eq, Ord, Read, Show)

_DataExactCardinality = (Core.Name "hydra/langs/owl/syntax.DataExactCardinality")

_DataExactCardinality_bound = (Core.FieldName "bound")

_DataExactCardinality_property = (Core.FieldName "property")

_DataExactCardinality_range = (Core.FieldName "range")

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

_Axiom_annotationAxiom = (Core.FieldName "annotationAxiom")

_Axiom_assertion = (Core.FieldName "assertion")

_Axiom_classAxiom = (Core.FieldName "classAxiom")

_Axiom_dataPropertyAxiom = (Core.FieldName "dataPropertyAxiom")

_Axiom_datatypeDefinition = (Core.FieldName "datatypeDefinition")

_Axiom_declaration = (Core.FieldName "declaration")

_Axiom_hasKey = (Core.FieldName "hasKey")

_Axiom_objectPropertyAxiom = (Core.FieldName "objectPropertyAxiom")

data ClassAxiom = 
  ClassAxiomDisjointClasses DisjointClasses |
  ClassAxiomDisjointUnion DisjointUnion |
  ClassAxiomEquivalentClasses EquivalentClasses |
  ClassAxiomSubClassOf SubClassOf
  deriving (Eq, Ord, Read, Show)

_ClassAxiom = (Core.Name "hydra/langs/owl/syntax.ClassAxiom")

_ClassAxiom_disjointClasses = (Core.FieldName "disjointClasses")

_ClassAxiom_disjointUnion = (Core.FieldName "disjointUnion")

_ClassAxiom_equivalentClasses = (Core.FieldName "equivalentClasses")

_ClassAxiom_subClassOf = (Core.FieldName "subClassOf")

data SubClassOf = 
  SubClassOf {
    subClassOfAnnotations :: [Annotation],
    subClassOfSubClass :: ClassExpression,
    subClassOfSuperClass :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_SubClassOf = (Core.Name "hydra/langs/owl/syntax.SubClassOf")

_SubClassOf_annotations = (Core.FieldName "annotations")

_SubClassOf_subClass = (Core.FieldName "subClass")

_SubClassOf_superClass = (Core.FieldName "superClass")

data EquivalentClasses = 
  EquivalentClasses {
    equivalentClassesAnnotations :: [Annotation],
    equivalentClassesClasses :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_EquivalentClasses = (Core.Name "hydra/langs/owl/syntax.EquivalentClasses")

_EquivalentClasses_annotations = (Core.FieldName "annotations")

_EquivalentClasses_classes = (Core.FieldName "classes")

data DisjointClasses = 
  DisjointClasses {
    disjointClassesAnnotations :: [Annotation],
    disjointClassesClasses :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_DisjointClasses = (Core.Name "hydra/langs/owl/syntax.DisjointClasses")

_DisjointClasses_annotations = (Core.FieldName "annotations")

_DisjointClasses_classes = (Core.FieldName "classes")

-- | See https://www.w3.org/TR/owl2-syntax/#Disjoint_Union_of_Class_Expressions
data DisjointUnion = 
  DisjointUnion {
    disjointUnionAnnotations :: [Annotation],
    disjointUnionClass :: Class,
    disjointUnionClasses :: [ClassExpression]}
  deriving (Eq, Ord, Read, Show)

_DisjointUnion = (Core.Name "hydra/langs/owl/syntax.DisjointUnion")

_DisjointUnion_annotations = (Core.FieldName "annotations")

_DisjointUnion_class = (Core.FieldName "class")

_DisjointUnion_classes = (Core.FieldName "classes")

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

_ObjectPropertyAxiom_asymmetricObjectProperty = (Core.FieldName "asymmetricObjectProperty")

_ObjectPropertyAxiom_disjointObjectProperties = (Core.FieldName "disjointObjectProperties")

_ObjectPropertyAxiom_equivalentObjectProperties = (Core.FieldName "equivalentObjectProperties")

_ObjectPropertyAxiom_functionalObjectProperty = (Core.FieldName "functionalObjectProperty")

_ObjectPropertyAxiom_inverseFunctionalObjectProperty = (Core.FieldName "inverseFunctionalObjectProperty")

_ObjectPropertyAxiom_inverseObjectProperties = (Core.FieldName "inverseObjectProperties")

_ObjectPropertyAxiom_irreflexiveObjectProperty = (Core.FieldName "irreflexiveObjectProperty")

_ObjectPropertyAxiom_objectPropertyDomain = (Core.FieldName "objectPropertyDomain")

_ObjectPropertyAxiom_objectPropertyRange = (Core.FieldName "objectPropertyRange")

_ObjectPropertyAxiom_reflexiveObjectProperty = (Core.FieldName "reflexiveObjectProperty")

_ObjectPropertyAxiom_subObjectPropertyOf = (Core.FieldName "subObjectPropertyOf")

_ObjectPropertyAxiom_symmetricObjectProperty = (Core.FieldName "symmetricObjectProperty")

_ObjectPropertyAxiom_transitiveObjectProperty = (Core.FieldName "transitiveObjectProperty")

data SubObjectPropertyOf = 
  SubObjectPropertyOf {
    subObjectPropertyOfAnnotations :: [Annotation],
    subObjectPropertyOfSubProperty :: [ObjectPropertyExpression],
    subObjectPropertyOfSuperProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_SubObjectPropertyOf = (Core.Name "hydra/langs/owl/syntax.SubObjectPropertyOf")

_SubObjectPropertyOf_annotations = (Core.FieldName "annotations")

_SubObjectPropertyOf_subProperty = (Core.FieldName "subProperty")

_SubObjectPropertyOf_superProperty = (Core.FieldName "superProperty")

data EquivalentObjectProperties = 
  EquivalentObjectProperties {
    equivalentObjectPropertiesAnnotations :: [Annotation],
    equivalentObjectPropertiesProperties :: [ObjectPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_EquivalentObjectProperties = (Core.Name "hydra/langs/owl/syntax.EquivalentObjectProperties")

_EquivalentObjectProperties_annotations = (Core.FieldName "annotations")

_EquivalentObjectProperties_properties = (Core.FieldName "properties")

data DisjointObjectProperties = 
  DisjointObjectProperties {
    disjointObjectPropertiesAnnotations :: [Annotation],
    disjointObjectPropertiesProperties :: [ObjectPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_DisjointObjectProperties = (Core.Name "hydra/langs/owl/syntax.DisjointObjectProperties")

_DisjointObjectProperties_annotations = (Core.FieldName "annotations")

_DisjointObjectProperties_properties = (Core.FieldName "properties")

-- | See https://www.w3.org/TR/owl2-syntax/#Object_Property_Domain
data ObjectPropertyDomain = 
  ObjectPropertyDomain {
    objectPropertyDomainAnnotations :: [Annotation],
    objectPropertyDomainProperty :: ObjectPropertyExpression,
    objectPropertyDomainDomain :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_ObjectPropertyDomain = (Core.Name "hydra/langs/owl/syntax.ObjectPropertyDomain")

_ObjectPropertyDomain_annotations = (Core.FieldName "annotations")

_ObjectPropertyDomain_property = (Core.FieldName "property")

_ObjectPropertyDomain_domain = (Core.FieldName "domain")

-- | See https://www.w3.org/TR/owl2-syntax/#Object_Property_Range
data ObjectPropertyRange = 
  ObjectPropertyRange {
    objectPropertyRangeAnnotations :: [Annotation],
    objectPropertyRangeProperty :: ObjectPropertyExpression,
    objectPropertyRangeRange :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_ObjectPropertyRange = (Core.Name "hydra/langs/owl/syntax.ObjectPropertyRange")

_ObjectPropertyRange_annotations = (Core.FieldName "annotations")

_ObjectPropertyRange_property = (Core.FieldName "property")

_ObjectPropertyRange_range = (Core.FieldName "range")

data InverseObjectProperties = 
  InverseObjectProperties {
    inverseObjectPropertiesAnnotations :: [Annotation],
    inverseObjectPropertiesProperty1 :: ObjectPropertyExpression,
    inverseObjectPropertiesProperty2 :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_InverseObjectProperties = (Core.Name "hydra/langs/owl/syntax.InverseObjectProperties")

_InverseObjectProperties_annotations = (Core.FieldName "annotations")

_InverseObjectProperties_property1 = (Core.FieldName "property1")

_InverseObjectProperties_property2 = (Core.FieldName "property2")

data FunctionalObjectProperty = 
  FunctionalObjectProperty {
    functionalObjectPropertyAnnotations :: [Annotation],
    functionalObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_FunctionalObjectProperty = (Core.Name "hydra/langs/owl/syntax.FunctionalObjectProperty")

_FunctionalObjectProperty_annotations = (Core.FieldName "annotations")

_FunctionalObjectProperty_property = (Core.FieldName "property")

data InverseFunctionalObjectProperty = 
  InverseFunctionalObjectProperty {
    inverseFunctionalObjectPropertyAnnotations :: [Annotation],
    inverseFunctionalObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_InverseFunctionalObjectProperty = (Core.Name "hydra/langs/owl/syntax.InverseFunctionalObjectProperty")

_InverseFunctionalObjectProperty_annotations = (Core.FieldName "annotations")

_InverseFunctionalObjectProperty_property = (Core.FieldName "property")

data ReflexiveObjectProperty = 
  ReflexiveObjectProperty {
    reflexiveObjectPropertyAnnotations :: [Annotation],
    reflexiveObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_ReflexiveObjectProperty = (Core.Name "hydra/langs/owl/syntax.ReflexiveObjectProperty")

_ReflexiveObjectProperty_annotations = (Core.FieldName "annotations")

_ReflexiveObjectProperty_property = (Core.FieldName "property")

data IrreflexiveObjectProperty = 
  IrreflexiveObjectProperty {
    irreflexiveObjectPropertyAnnotations :: [Annotation],
    irreflexiveObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_IrreflexiveObjectProperty = (Core.Name "hydra/langs/owl/syntax.IrreflexiveObjectProperty")

_IrreflexiveObjectProperty_annotations = (Core.FieldName "annotations")

_IrreflexiveObjectProperty_property = (Core.FieldName "property")

data SymmetricObjectProperty = 
  SymmetricObjectProperty {
    symmetricObjectPropertyAnnotations :: [Annotation],
    symmetricObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_SymmetricObjectProperty = (Core.Name "hydra/langs/owl/syntax.SymmetricObjectProperty")

_SymmetricObjectProperty_annotations = (Core.FieldName "annotations")

_SymmetricObjectProperty_property = (Core.FieldName "property")

data AsymmetricObjectProperty = 
  AsymmetricObjectProperty {
    asymmetricObjectPropertyAnnotations :: [Annotation],
    asymmetricObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_AsymmetricObjectProperty = (Core.Name "hydra/langs/owl/syntax.AsymmetricObjectProperty")

_AsymmetricObjectProperty_annotations = (Core.FieldName "annotations")

_AsymmetricObjectProperty_property = (Core.FieldName "property")

data TransitiveObjectProperty = 
  TransitiveObjectProperty {
    transitiveObjectPropertyAnnotations :: [Annotation],
    transitiveObjectPropertyProperty :: ObjectPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_TransitiveObjectProperty = (Core.Name "hydra/langs/owl/syntax.TransitiveObjectProperty")

_TransitiveObjectProperty_annotations = (Core.FieldName "annotations")

_TransitiveObjectProperty_property = (Core.FieldName "property")

data DataPropertyAxiom = 
  DataPropertyAxiomDataPropertyAxiom DataPropertyAxiom |
  DataPropertyAxiomDataPropertyRange DataPropertyRange |
  DataPropertyAxiomDisjointDataProperties DisjointDataProperties |
  DataPropertyAxiomEquivalentDataProperties EquivalentDataProperties |
  DataPropertyAxiomFunctionalDataProperty FunctionalDataProperty |
  DataPropertyAxiomSubDataPropertyOf SubDataPropertyOf
  deriving (Eq, Ord, Read, Show)

_DataPropertyAxiom = (Core.Name "hydra/langs/owl/syntax.DataPropertyAxiom")

_DataPropertyAxiom_dataPropertyAxiom = (Core.FieldName "dataPropertyAxiom")

_DataPropertyAxiom_dataPropertyRange = (Core.FieldName "dataPropertyRange")

_DataPropertyAxiom_disjointDataProperties = (Core.FieldName "disjointDataProperties")

_DataPropertyAxiom_equivalentDataProperties = (Core.FieldName "equivalentDataProperties")

_DataPropertyAxiom_functionalDataProperty = (Core.FieldName "functionalDataProperty")

_DataPropertyAxiom_subDataPropertyOf = (Core.FieldName "subDataPropertyOf")

data SubDataPropertyOf = 
  SubDataPropertyOf {
    subDataPropertyOfAnnotations :: [Annotation],
    subDataPropertyOfSubProperty :: DataPropertyExpression,
    subDataPropertyOfSuperProperty :: DataPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_SubDataPropertyOf = (Core.Name "hydra/langs/owl/syntax.SubDataPropertyOf")

_SubDataPropertyOf_annotations = (Core.FieldName "annotations")

_SubDataPropertyOf_subProperty = (Core.FieldName "subProperty")

_SubDataPropertyOf_superProperty = (Core.FieldName "superProperty")

data EquivalentDataProperties = 
  EquivalentDataProperties {
    equivalentDataPropertiesAnnotations :: [Annotation],
    equivalentDataPropertiesProperties :: [DataPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_EquivalentDataProperties = (Core.Name "hydra/langs/owl/syntax.EquivalentDataProperties")

_EquivalentDataProperties_annotations = (Core.FieldName "annotations")

_EquivalentDataProperties_properties = (Core.FieldName "properties")

data DisjointDataProperties = 
  DisjointDataProperties {
    disjointDataPropertiesAnnotations :: [Annotation],
    disjointDataPropertiesProperties :: [DataPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_DisjointDataProperties = (Core.Name "hydra/langs/owl/syntax.DisjointDataProperties")

_DisjointDataProperties_annotations = (Core.FieldName "annotations")

_DisjointDataProperties_properties = (Core.FieldName "properties")

data DataPropertyDomain = 
  DataPropertyDomain {
    dataPropertyDomainAnnotations :: [Annotation],
    dataPropertyDomainProperty :: DataPropertyExpression,
    dataPropertyDomainDomain :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_DataPropertyDomain = (Core.Name "hydra/langs/owl/syntax.DataPropertyDomain")

_DataPropertyDomain_annotations = (Core.FieldName "annotations")

_DataPropertyDomain_property = (Core.FieldName "property")

_DataPropertyDomain_domain = (Core.FieldName "domain")

data DataPropertyRange = 
  DataPropertyRange {
    dataPropertyRangeAnnotations :: [Annotation],
    dataPropertyRangeProperty :: DataPropertyExpression,
    dataPropertyRangeRange :: ClassExpression}
  deriving (Eq, Ord, Read, Show)

_DataPropertyRange = (Core.Name "hydra/langs/owl/syntax.DataPropertyRange")

_DataPropertyRange_annotations = (Core.FieldName "annotations")

_DataPropertyRange_property = (Core.FieldName "property")

_DataPropertyRange_range = (Core.FieldName "range")

data FunctionalDataProperty = 
  FunctionalDataProperty {
    functionalDataPropertyAnnotations :: [Annotation],
    functionalDataPropertyProperty :: DataPropertyExpression}
  deriving (Eq, Ord, Read, Show)

_FunctionalDataProperty = (Core.Name "hydra/langs/owl/syntax.FunctionalDataProperty")

_FunctionalDataProperty_annotations = (Core.FieldName "annotations")

_FunctionalDataProperty_property = (Core.FieldName "property")

data DatatypeDefinition = 
  DatatypeDefinition {
    datatypeDefinitionAnnotations :: [Annotation],
    datatypeDefinitionDatatype :: Datatype,
    datatypeDefinitionRange :: DataRange}
  deriving (Eq, Ord, Read, Show)

_DatatypeDefinition = (Core.Name "hydra/langs/owl/syntax.DatatypeDefinition")

_DatatypeDefinition_annotations = (Core.FieldName "annotations")

_DatatypeDefinition_datatype = (Core.FieldName "datatype")

_DatatypeDefinition_range = (Core.FieldName "range")

-- | See https://www.w3.org/TR/owl2-syntax/#Keys
data HasKey = 
  HasKey {
    hasKeyAnnotations :: [Annotation],
    hasKeyClass :: ClassExpression,
    hasKeyObjectProperties :: [ObjectPropertyExpression],
    hasKeyDataProperties :: [DataPropertyExpression]}
  deriving (Eq, Ord, Read, Show)

_HasKey = (Core.Name "hydra/langs/owl/syntax.HasKey")

_HasKey_annotations = (Core.FieldName "annotations")

_HasKey_class = (Core.FieldName "class")

_HasKey_objectProperties = (Core.FieldName "objectProperties")

_HasKey_dataProperties = (Core.FieldName "dataProperties")

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

_Assertion_classAssertion = (Core.FieldName "classAssertion")

_Assertion_dataPropertyAssertion = (Core.FieldName "dataPropertyAssertion")

_Assertion_differentIndividuals = (Core.FieldName "differentIndividuals")

_Assertion_objectPropertyAssertion = (Core.FieldName "objectPropertyAssertion")

_Assertion_negativeDataPropertyAssertion = (Core.FieldName "negativeDataPropertyAssertion")

_Assertion_negativeObjectPropertyAssertion = (Core.FieldName "negativeObjectPropertyAssertion")

_Assertion_sameIndividual = (Core.FieldName "sameIndividual")

data SameIndividual = 
  SameIndividual {
    sameIndividualAnnotations :: [Annotation],
    sameIndividualIndividuals :: [Individual]}
  deriving (Eq, Ord, Read, Show)

_SameIndividual = (Core.Name "hydra/langs/owl/syntax.SameIndividual")

_SameIndividual_annotations = (Core.FieldName "annotations")

_SameIndividual_individuals = (Core.FieldName "individuals")

data DifferentIndividuals = 
  DifferentIndividuals {
    differentIndividualsAnnotations :: [Annotation],
    differentIndividualsIndividuals :: [Individual]}
  deriving (Eq, Ord, Read, Show)

_DifferentIndividuals = (Core.Name "hydra/langs/owl/syntax.DifferentIndividuals")

_DifferentIndividuals_annotations = (Core.FieldName "annotations")

_DifferentIndividuals_individuals = (Core.FieldName "individuals")

data ClassAssertion = 
  ClassAssertion {
    classAssertionAnnotations :: [Annotation],
    classAssertionClass :: ClassExpression,
    classAssertionIndividual :: Individual}
  deriving (Eq, Ord, Read, Show)

_ClassAssertion = (Core.Name "hydra/langs/owl/syntax.ClassAssertion")

_ClassAssertion_annotations = (Core.FieldName "annotations")

_ClassAssertion_class = (Core.FieldName "class")

_ClassAssertion_individual = (Core.FieldName "individual")

data ObjectPropertyAssertion = 
  ObjectPropertyAssertion {
    objectPropertyAssertionAnnotations :: [Annotation],
    objectPropertyAssertionProperty :: ObjectPropertyExpression,
    objectPropertyAssertionSource :: Individual,
    objectPropertyAssertionTarget :: Individual}
  deriving (Eq, Ord, Read, Show)

_ObjectPropertyAssertion = (Core.Name "hydra/langs/owl/syntax.ObjectPropertyAssertion")

_ObjectPropertyAssertion_annotations = (Core.FieldName "annotations")

_ObjectPropertyAssertion_property = (Core.FieldName "property")

_ObjectPropertyAssertion_source = (Core.FieldName "source")

_ObjectPropertyAssertion_target = (Core.FieldName "target")

data NegativeObjectPropertyAssertion = 
  NegativeObjectPropertyAssertion {
    negativeObjectPropertyAssertionAnnotations :: [Annotation],
    negativeObjectPropertyAssertionProperty :: ObjectPropertyExpression,
    negativeObjectPropertyAssertionSource :: Individual,
    negativeObjectPropertyAssertionTarget :: Individual}
  deriving (Eq, Ord, Read, Show)

_NegativeObjectPropertyAssertion = (Core.Name "hydra/langs/owl/syntax.NegativeObjectPropertyAssertion")

_NegativeObjectPropertyAssertion_annotations = (Core.FieldName "annotations")

_NegativeObjectPropertyAssertion_property = (Core.FieldName "property")

_NegativeObjectPropertyAssertion_source = (Core.FieldName "source")

_NegativeObjectPropertyAssertion_target = (Core.FieldName "target")

data DataPropertyAssertion = 
  DataPropertyAssertion {
    dataPropertyAssertionAnnotations :: [Annotation],
    dataPropertyAssertionProperty :: DataPropertyExpression,
    dataPropertyAssertionSource :: Individual,
    dataPropertyAssertionTarget :: Individual}
  deriving (Eq, Ord, Read, Show)

_DataPropertyAssertion = (Core.Name "hydra/langs/owl/syntax.DataPropertyAssertion")

_DataPropertyAssertion_annotations = (Core.FieldName "annotations")

_DataPropertyAssertion_property = (Core.FieldName "property")

_DataPropertyAssertion_source = (Core.FieldName "source")

_DataPropertyAssertion_target = (Core.FieldName "target")

data NegativeDataPropertyAssertion = 
  NegativeDataPropertyAssertion {
    negativeDataPropertyAssertionAnnotations :: [Annotation],
    negativeDataPropertyAssertionProperty :: DataPropertyExpression,
    negativeDataPropertyAssertionSource :: Individual,
    negativeDataPropertyAssertionTarget :: Individual}
  deriving (Eq, Ord, Read, Show)

_NegativeDataPropertyAssertion = (Core.Name "hydra/langs/owl/syntax.NegativeDataPropertyAssertion")

_NegativeDataPropertyAssertion_annotations = (Core.FieldName "annotations")

_NegativeDataPropertyAssertion_property = (Core.FieldName "property")

_NegativeDataPropertyAssertion_source = (Core.FieldName "source")

_NegativeDataPropertyAssertion_target = (Core.FieldName "target")