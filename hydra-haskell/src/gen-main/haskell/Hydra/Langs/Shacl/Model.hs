-- | A SHACL syntax model. See https://www.w3.org/TR/shacl

module Hydra.Langs.Shacl.Model where

import qualified Hydra.Core as Core
import qualified Hydra.Langs.Rdf.Syntax as Syntax
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | See https://www.w3.org/TR/shacl/#ClosedPatterConstraintComponent
data Closed = 
  Closed {
    closedIsClosed :: Bool,
    closedIgnoredProperties :: (Maybe (Set Syntax.Property))}
  deriving (Eq, Ord, Read, Show)

_Closed = (Core.Name "hydra/langs/shacl/model.Closed")

_Closed_isClosed = (Core.FieldName "isClosed")

_Closed_ignoredProperties = (Core.FieldName "ignoredProperties")

-- | Any of a number of constraint parameters which can be applied either to node or property shapes
data CommonConstraint = 
  -- | See https://www.w3.org/TR/shacl/#AndConstraintComponent
  CommonConstraintAnd (Set (Reference Shape)) |
  -- | See https://www.w3.org/TR/shacl/#ClosedConstraintComponent
  CommonConstraintClosed Closed |
  -- | See https://www.w3.org/TR/shacl/#ClassConstraintComponent
  CommonConstraintClass (Set Syntax.RdfsClass) |
  -- | See https://www.w3.org/TR/shacl/#DatatypeConstraintComponent
  CommonConstraintDatatype Syntax.Iri |
  -- | See https://www.w3.org/TR/shacl/#DisjointConstraintComponent
  CommonConstraintDisjoint (Set Syntax.Property) |
  -- | See https://www.w3.org/TR/shacl/#EqualsConstraintComponent
  CommonConstraintEquals (Set Syntax.Property) |
  -- | Specifies the condition that at least one value node is equal to the given RDF term. See https://www.w3.org/TR/shacl/#HasValueConstraintComponent
  CommonConstraintHasValue (Set Syntax.Node) |
  -- | Specifies the condition that each value node is a member of a provided SHACL list. See https://www.w3.org/TR/shacl/#InConstraintComponent
  CommonConstraintIn [Syntax.Node] |
  -- | See https://www.w3.org/TR/shacl/#LanguageInConstraintComponent
  CommonConstraintLanguageIn (Set Syntax.LanguageTag) |
  -- | See https://www.w3.org/TR/shacl/#NodeKindConstraintComponent
  CommonConstraintNodeKind NodeKind |
  -- | See https://www.w3.org/TR/shacl/#NodeConstraintComponent
  CommonConstraintNode (Set (Reference NodeShape)) |
  -- | See https://www.w3.org/TR/shacl/#NotConstraintComponent
  CommonConstraintNot (Set (Reference Shape)) |
  -- | See https://www.w3.org/TR/shacl/#MaxExclusiveConstraintComponent
  CommonConstraintMaxExclusive Syntax.Literal |
  -- | See https://www.w3.org/TR/shacl/#MaxInclusiveConstraintComponent
  CommonConstraintMaxInclusive Syntax.Literal |
  -- | See https://www.w3.org/TR/shacl/#MaxLengthConstraintComponent
  CommonConstraintMaxLength Integer |
  -- | See https://www.w3.org/TR/shacl/#MinExclusiveConstraintComponent
  CommonConstraintMinExclusive Syntax.Literal |
  -- | See https://www.w3.org/TR/shacl/#MinInclusiveConstraintComponent
  CommonConstraintMinInclusive Syntax.Literal |
  -- | See https://www.w3.org/TR/shacl/#MinLengthConstraintComponent
  CommonConstraintMinLength Integer |
  -- | See https://www.w3.org/TR/shacl/#PatternConstraintComponent
  CommonConstraintPattern Pattern |
  -- | See https://www.w3.org/TR/shacl/#PropertyConstraintComponent
  CommonConstraintProperty (Set (Reference PropertyShape)) |
  -- | See https://www.w3.org/TR/shacl/#OrConstraintComponent
  CommonConstraintOr (Set (Reference Shape)) |
  -- | See https://www.w3.org/TR/shacl/#XoneConstraintComponent
  CommonConstraintXone (Set (Reference Shape))
  deriving (Eq, Ord, Read, Show)

_CommonConstraint = (Core.Name "hydra/langs/shacl/model.CommonConstraint")

_CommonConstraint_and = (Core.FieldName "and")

_CommonConstraint_closed = (Core.FieldName "closed")

_CommonConstraint_class = (Core.FieldName "class")

_CommonConstraint_datatype = (Core.FieldName "datatype")

_CommonConstraint_disjoint = (Core.FieldName "disjoint")

_CommonConstraint_equals = (Core.FieldName "equals")

_CommonConstraint_hasValue = (Core.FieldName "hasValue")

_CommonConstraint_in = (Core.FieldName "in")

_CommonConstraint_languageIn = (Core.FieldName "languageIn")

_CommonConstraint_nodeKind = (Core.FieldName "nodeKind")

_CommonConstraint_node = (Core.FieldName "node")

_CommonConstraint_not = (Core.FieldName "not")

_CommonConstraint_maxExclusive = (Core.FieldName "maxExclusive")

_CommonConstraint_maxInclusive = (Core.FieldName "maxInclusive")

_CommonConstraint_maxLength = (Core.FieldName "maxLength")

_CommonConstraint_minExclusive = (Core.FieldName "minExclusive")

_CommonConstraint_minInclusive = (Core.FieldName "minInclusive")

_CommonConstraint_minLength = (Core.FieldName "minLength")

_CommonConstraint_pattern = (Core.FieldName "pattern")

_CommonConstraint_property = (Core.FieldName "property")

_CommonConstraint_or = (Core.FieldName "or")

_CommonConstraint_xone = (Core.FieldName "xone")

-- | Common constraint parameters and other properties for SHACL shapes
data CommonProperties = 
  CommonProperties {
    -- | Common constraint parameters attached to this shape
    commonPropertiesConstraints :: (Set CommonConstraint),
    -- | See https://www.w3.org/TR/shacl/#deactivated
    commonPropertiesDeactivated :: (Maybe Bool),
    -- | See https://www.w3.org/TR/shacl/#message
    commonPropertiesMessage :: Syntax.LangStrings,
    -- | See https://www.w3.org/TR/shacl/#severity
    commonPropertiesSeverity :: Severity,
    -- | See https://www.w3.org/TR/shacl/#targetClass
    commonPropertiesTargetClass :: (Set Syntax.RdfsClass),
    -- | See https://www.w3.org/TR/shacl/#targetNode
    commonPropertiesTargetNode :: (Set Syntax.IriOrLiteral),
    -- | See https://www.w3.org/TR/shacl/#targetObjectsOf
    commonPropertiesTargetObjectsOf :: (Set Syntax.Property),
    -- | See https://www.w3.org/TR/shacl/#targetSubjectsOf
    commonPropertiesTargetSubjectsOf :: (Set Syntax.Property)}
  deriving (Eq, Ord, Read, Show)

_CommonProperties = (Core.Name "hydra/langs/shacl/model.CommonProperties")

_CommonProperties_constraints = (Core.FieldName "constraints")

_CommonProperties_deactivated = (Core.FieldName "deactivated")

_CommonProperties_message = (Core.FieldName "message")

_CommonProperties_severity = (Core.FieldName "severity")

_CommonProperties_targetClass = (Core.FieldName "targetClass")

_CommonProperties_targetNode = (Core.FieldName "targetNode")

_CommonProperties_targetObjectsOf = (Core.FieldName "targetObjectsOf")

_CommonProperties_targetSubjectsOf = (Core.FieldName "targetSubjectsOf")

-- | An instance of a type like sh:Shape or sh:NodeShape, together with a unique IRI for that instance
data Definition a = 
  Definition {
    definitionIri :: Syntax.Iri,
    definitionTarget :: a}
  deriving (Eq, Ord, Read, Show)

_Definition = (Core.Name "hydra/langs/shacl/model.Definition")

_Definition_iri = (Core.FieldName "iri")

_Definition_target = (Core.FieldName "target")

data NodeKind = 
  -- | A blank node
  NodeKindBlankNode  |
  -- | An IRI
  NodeKindIri  |
  -- | A literal
  NodeKindLiteral  |
  -- | A blank node or an IRI
  NodeKindBlankNodeOrIri  |
  -- | A blank node or a literal
  NodeKindBlankNodeOrLiteral  |
  -- | An IRI or a literal
  NodeKindIriOrLiteral 
  deriving (Eq, Ord, Read, Show)

_NodeKind = (Core.Name "hydra/langs/shacl/model.NodeKind")

_NodeKind_blankNode = (Core.FieldName "blankNode")

_NodeKind_iri = (Core.FieldName "iri")

_NodeKind_literal = (Core.FieldName "literal")

_NodeKind_blankNodeOrIri = (Core.FieldName "blankNodeOrIri")

_NodeKind_blankNodeOrLiteral = (Core.FieldName "blankNodeOrLiteral")

_NodeKind_iriOrLiteral = (Core.FieldName "iriOrLiteral")

-- | A SHACL node shape. See https://www.w3.org/TR/shacl/#node-shapes
data NodeShape = 
  NodeShape {
    nodeShapeCommon :: CommonProperties}
  deriving (Eq, Ord, Read, Show)

_NodeShape = (Core.Name "hydra/langs/shacl/model.NodeShape")

_NodeShape_common = (Core.FieldName "common")

-- | A SHACL pattern. See https://www.w3.org/TR/shacl/#PatternConstraintComponent
data Pattern = 
  Pattern {
    patternRegex :: String,
    patternFlags :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Pattern = (Core.Name "hydra/langs/shacl/model.Pattern")

_Pattern_regex = (Core.FieldName "regex")

_Pattern_flags = (Core.FieldName "flags")

-- | A SHACL property shape. See https://www.w3.org/TR/shacl/#property-shapes
data PropertyShape = 
  PropertyShape {
    propertyShapeCommon :: CommonProperties,
    -- | Any property shape -specific constraint parameters
    propertyShapeConstraints :: (Set PropertyShapeConstraint),
    -- | See https://www.w3.org/TR/shacl/#defaultValue
    propertyShapeDefaultValue :: (Maybe Syntax.Node),
    -- | See https://www.w3.org/TR/shacl/#name
    propertyShapeDescription :: Syntax.LangStrings,
    -- | See https://www.w3.org/TR/shacl/#name
    propertyShapeName :: Syntax.LangStrings,
    -- | See https://www.w3.org/TR/shacl/#order
    propertyShapeOrder :: (Maybe Integer),
    propertyShapePath :: Syntax.Iri}
  deriving (Eq, Ord, Read, Show)

_PropertyShape = (Core.Name "hydra/langs/shacl/model.PropertyShape")

_PropertyShape_common = (Core.FieldName "common")

_PropertyShape_constraints = (Core.FieldName "constraints")

_PropertyShape_defaultValue = (Core.FieldName "defaultValue")

_PropertyShape_description = (Core.FieldName "description")

_PropertyShape_name = (Core.FieldName "name")

_PropertyShape_order = (Core.FieldName "order")

_PropertyShape_path = (Core.FieldName "path")

-- | A number of constraint parameters which are specific to property shapes, and cannot be applied to node shapes
data PropertyShapeConstraint = 
  -- | See https://www.w3.org/TR/shacl/#LessThanConstraintComponent
  PropertyShapeConstraintLessThan (Set Syntax.Property) |
  -- | See https://www.w3.org/TR/shacl/#LessThanOrEqualsConstraintComponent
  PropertyShapeConstraintLessThanOrEquals (Set Syntax.Property) |
  -- | The maximum cardinality. Node shapes cannot have any value for sh:maxCount. See https://www.w3.org/TR/shacl/#MaxCountConstraintComponent
  PropertyShapeConstraintMaxCount Integer |
  -- | The minimum cardinality. Node shapes cannot have any value for sh:minCount. See https://www.w3.org/TR/shacl/#MinCountConstraintComponent
  PropertyShapeConstraintMinCount Integer |
  -- | See https://www.w3.org/TR/shacl/#UniqueLangConstraintComponent
  PropertyShapeConstraintUniqueLang Bool |
  -- | See https://www.w3.org/TR/shacl/#QualifiedValueShapeConstraintComponent
  PropertyShapeConstraintQualifiedValueShape QualifiedValueShape
  deriving (Eq, Ord, Read, Show)

_PropertyShapeConstraint = (Core.Name "hydra/langs/shacl/model.PropertyShapeConstraint")

_PropertyShapeConstraint_lessThan = (Core.FieldName "lessThan")

_PropertyShapeConstraint_lessThanOrEquals = (Core.FieldName "lessThanOrEquals")

_PropertyShapeConstraint_maxCount = (Core.FieldName "maxCount")

_PropertyShapeConstraint_minCount = (Core.FieldName "minCount")

_PropertyShapeConstraint_uniqueLang = (Core.FieldName "uniqueLang")

_PropertyShapeConstraint_qualifiedValueShape = (Core.FieldName "qualifiedValueShape")

-- | See https://www.w3.org/TR/shacl/#QualifiedValueShapeConstraintComponent
data QualifiedValueShape = 
  QualifiedValueShape {
    qualifiedValueShapeQualifiedValueShape :: (Reference Shape),
    qualifiedValueShapeQualifiedMaxCount :: Integer,
    qualifiedValueShapeQualifiedMinCount :: Integer,
    qualifiedValueShapeQualifiedValueShapesDisjoint :: (Maybe Bool)}
  deriving (Eq, Ord, Read, Show)

_QualifiedValueShape = (Core.Name "hydra/langs/shacl/model.QualifiedValueShape")

_QualifiedValueShape_qualifiedValueShape = (Core.FieldName "qualifiedValueShape")

_QualifiedValueShape_qualifiedMaxCount = (Core.FieldName "qualifiedMaxCount")

_QualifiedValueShape_qualifiedMinCount = (Core.FieldName "qualifiedMinCount")

_QualifiedValueShape_qualifiedValueShapesDisjoint = (Core.FieldName "qualifiedValueShapesDisjoint")

-- | Either an instance of a type like sh:Shape or sh:NodeShape, or an IRI which refers to an instance of that type
data Reference a = 
  ReferenceNamed Syntax.Iri |
  -- | An anonymous instance
  ReferenceAnonymous a |
  -- | An inline definition
  ReferenceDefinition (Definition a)
  deriving (Eq, Ord, Read, Show)

_Reference = (Core.Name "hydra/langs/shacl/model.Reference")

_Reference_named = (Core.FieldName "named")

_Reference_anonymous = (Core.FieldName "anonymous")

_Reference_definition = (Core.FieldName "definition")

data Severity = 
  -- | A non-critical constraint violation indicating an informative message
  SeverityInfo  |
  -- | A non-critical constraint violation indicating a warning
  SeverityWarning  |
  -- | A constraint violation
  SeverityViolation 
  deriving (Eq, Ord, Read, Show)

_Severity = (Core.Name "hydra/langs/shacl/model.Severity")

_Severity_info = (Core.FieldName "info")

_Severity_warning = (Core.FieldName "warning")

_Severity_violation = (Core.FieldName "violation")

-- | A SHACL node or property shape. See https://www.w3.org/TR/shacl/#shapes
data Shape = 
  ShapeNode NodeShape |
  ShapeProperty PropertyShape
  deriving (Eq, Ord, Read, Show)

_Shape = (Core.Name "hydra/langs/shacl/model.Shape")

_Shape_node = (Core.FieldName "node")

_Shape_property = (Core.FieldName "property")

-- | An RDF graph containing zero or more shapes that is passed into a SHACL validation process so that a data graph can be validated against the shapes
newtype ShapesGraph = 
  ShapesGraph {
    -- | An RDF graph containing zero or more shapes that is passed into a SHACL validation process so that a data graph can be validated against the shapes
    unShapesGraph :: (Set (Definition Shape))}
  deriving (Eq, Ord, Read, Show)

_ShapesGraph = (Core.Name "hydra/langs/shacl/model.ShapesGraph")