-- | A Shex model. Based on the BNF at:
-- |   https://github.com/shexSpec/grammar/blob/master/bnf

module Hydra.Langs.Shex.Syntax where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

data ShexDoc = 
  ShexDoc {
    shexDocListOfDirective :: [Directive],
    shexDocSequence :: (Maybe ShexDoc_Sequence_Option),
    shexDocPrefixDecl :: PrefixDecl}
  deriving (Eq, Ord, Read, Show)

_ShexDoc = (Core.Name "hydra/langs/shex/syntax.ShexDoc")

_ShexDoc_listOfDirective = (Core.FieldName "listOfDirective")

_ShexDoc_sequence = (Core.FieldName "sequence")

_ShexDoc_prefixDecl = (Core.FieldName "prefixDecl")

data ShexDoc_Sequence_Option = 
  ShexDoc_Sequence_Option {
    shexDoc_Sequence_OptionAlts :: ShexDoc_Sequence_Option_Alts,
    shexDoc_Sequence_OptionListOfStatement :: [Statement]}
  deriving (Eq, Ord, Read, Show)

_ShexDoc_Sequence_Option = (Core.Name "hydra/langs/shex/syntax.ShexDoc.Sequence.Option")

_ShexDoc_Sequence_Option_alts = (Core.FieldName "alts")

_ShexDoc_Sequence_Option_listOfStatement = (Core.FieldName "listOfStatement")

data ShexDoc_Sequence_Option_Alts = 
  ShexDoc_Sequence_Option_AltsNotStartAction NotStartAction |
  ShexDoc_Sequence_Option_AltsStartActions StartActions
  deriving (Eq, Ord, Read, Show)

_ShexDoc_Sequence_Option_Alts = (Core.Name "hydra/langs/shex/syntax.ShexDoc.Sequence.Option.Alts")

_ShexDoc_Sequence_Option_Alts_notStartAction = (Core.FieldName "notStartAction")

_ShexDoc_Sequence_Option_Alts_startActions = (Core.FieldName "startActions")

data Directive = 
  DirectiveBaseDecl BaseDecl |
  DirectivePrefixDecl PrefixDecl
  deriving (Eq, Ord, Read, Show)

_Directive = (Core.Name "hydra/langs/shex/syntax.Directive")

_Directive_baseDecl = (Core.FieldName "baseDecl")

_Directive_prefixDecl = (Core.FieldName "prefixDecl")

newtype BaseDecl = 
  BaseDecl {
    unBaseDecl :: IriRef}
  deriving (Eq, Ord, Read, Show)

_BaseDecl = (Core.Name "hydra/langs/shex/syntax.BaseDecl")

data PrefixDecl = 
  PrefixDecl {
    prefixDeclPnameNs :: PnameNs,
    prefixDeclIriRef :: IriRef}
  deriving (Eq, Ord, Read, Show)

_PrefixDecl = (Core.Name "hydra/langs/shex/syntax.PrefixDecl")

_PrefixDecl_pnameNs = (Core.FieldName "pnameNs")

_PrefixDecl_iriRef = (Core.FieldName "iriRef")

data NotStartAction = 
  NotStartActionStart ShapeExpression |
  NotStartActionShapeExprDecl NotStartAction_ShapeExprDecl
  deriving (Eq, Ord, Read, Show)

_NotStartAction = (Core.Name "hydra/langs/shex/syntax.NotStartAction")

_NotStartAction_start = (Core.FieldName "start")

_NotStartAction_shapeExprDecl = (Core.FieldName "shapeExprDecl")

data NotStartAction_ShapeExprDecl = 
  NotStartAction_ShapeExprDecl {
    notStartAction_ShapeExprDeclShapeExprLabel :: ShapeExprLabel,
    notStartAction_ShapeExprDeclAlts :: NotStartAction_ShapeExprDecl_Alts}
  deriving (Eq, Ord, Read, Show)

_NotStartAction_ShapeExprDecl = (Core.Name "hydra/langs/shex/syntax.NotStartAction.ShapeExprDecl")

_NotStartAction_ShapeExprDecl_shapeExprLabel = (Core.FieldName "shapeExprLabel")

_NotStartAction_ShapeExprDecl_alts = (Core.FieldName "alts")

data NotStartAction_ShapeExprDecl_Alts = 
  NotStartAction_ShapeExprDecl_AltsShapeExpression ShapeExpression |
  NotStartAction_ShapeExprDecl_AltsEXTERNAL 
  deriving (Eq, Ord, Read, Show)

_NotStartAction_ShapeExprDecl_Alts = (Core.Name "hydra/langs/shex/syntax.NotStartAction.ShapeExprDecl.Alts")

_NotStartAction_ShapeExprDecl_Alts_shapeExpression = (Core.FieldName "shapeExpression")

_NotStartAction_ShapeExprDecl_Alts_eXTERNAL = (Core.FieldName "eXTERNAL")

newtype StartActions = 
  StartActions {
    unStartActions :: [CodeDecl]}
  deriving (Eq, Ord, Read, Show)

_StartActions = (Core.Name "hydra/langs/shex/syntax.StartActions")

data Statement = 
  StatementDirective Directive |
  StatementNotStartAction NotStartAction
  deriving (Eq, Ord, Read, Show)

_Statement = (Core.Name "hydra/langs/shex/syntax.Statement")

_Statement_directive = (Core.FieldName "directive")

_Statement_notStartAction = (Core.FieldName "notStartAction")

newtype ShapeExpression = 
  ShapeExpression {
    unShapeExpression :: ShapeOr}
  deriving (Eq, Ord, Read, Show)

_ShapeExpression = (Core.Name "hydra/langs/shex/syntax.ShapeExpression")

newtype InlineShapeExpression = 
  InlineShapeExpression {
    unInlineShapeExpression :: InlineShapeOr}
  deriving (Eq, Ord, Read, Show)

_InlineShapeExpression = (Core.Name "hydra/langs/shex/syntax.InlineShapeExpression")

data ShapeOr = 
  ShapeOr {
    shapeOrShapeAnd :: ShapeAnd,
    shapeOrListOfSequence :: [ShapeAnd]}
  deriving (Eq, Ord, Read, Show)

_ShapeOr = (Core.Name "hydra/langs/shex/syntax.ShapeOr")

_ShapeOr_shapeAnd = (Core.FieldName "shapeAnd")

_ShapeOr_listOfSequence = (Core.FieldName "listOfSequence")

data InlineShapeOr = 
  InlineShapeOr {
    inlineShapeOrShapeAnd :: ShapeAnd,
    inlineShapeOrListOfSequence :: [InlineShapeAnd]}
  deriving (Eq, Ord, Read, Show)

_InlineShapeOr = (Core.Name "hydra/langs/shex/syntax.InlineShapeOr")

_InlineShapeOr_shapeAnd = (Core.FieldName "shapeAnd")

_InlineShapeOr_listOfSequence = (Core.FieldName "listOfSequence")

data ShapeAnd = 
  ShapeAnd {
    shapeAndShapeNot :: ShapeNot,
    shapeAndListOfSequence :: [ShapeNot]}
  deriving (Eq, Ord, Read, Show)

_ShapeAnd = (Core.Name "hydra/langs/shex/syntax.ShapeAnd")

_ShapeAnd_shapeNot = (Core.FieldName "shapeNot")

_ShapeAnd_listOfSequence = (Core.FieldName "listOfSequence")

data InlineShapeAnd = 
  InlineShapeAnd {
    inlineShapeAndInlineShapeNot :: InlineShapeNot,
    inlineShapeAndListOfSequence :: [InlineShapeNot]}
  deriving (Eq, Ord, Read, Show)

_InlineShapeAnd = (Core.Name "hydra/langs/shex/syntax.InlineShapeAnd")

_InlineShapeAnd_inlineShapeNot = (Core.FieldName "inlineShapeNot")

_InlineShapeAnd_listOfSequence = (Core.FieldName "listOfSequence")

data ShapeNot = 
  ShapeNot {
    shapeNotNOT :: (Maybe ()),
    shapeNotShapeAtom :: ShapeAtom}
  deriving (Eq, Ord, Read, Show)

_ShapeNot = (Core.Name "hydra/langs/shex/syntax.ShapeNot")

_ShapeNot_nOT = (Core.FieldName "nOT")

_ShapeNot_shapeAtom = (Core.FieldName "shapeAtom")

data InlineShapeNot = 
  InlineShapeNot {
    inlineShapeNotNOT :: (Maybe ()),
    inlineShapeNotInlineShapeAtom :: InlineShapeAtom}
  deriving (Eq, Ord, Read, Show)

_InlineShapeNot = (Core.Name "hydra/langs/shex/syntax.InlineShapeNot")

_InlineShapeNot_nOT = (Core.FieldName "nOT")

_InlineShapeNot_inlineShapeAtom = (Core.FieldName "inlineShapeAtom")

data ShapeAtom = 
  ShapeAtomSequence ShapeAtom_Sequence |
  ShapeAtomShapeOrRef ShapeOrRef |
  ShapeAtomSequence2 ShapeExpression |
  ShapeAtomPeriod 
  deriving (Eq, Ord, Read, Show)

_ShapeAtom = (Core.Name "hydra/langs/shex/syntax.ShapeAtom")

_ShapeAtom_sequence = (Core.FieldName "sequence")

_ShapeAtom_shapeOrRef = (Core.FieldName "shapeOrRef")

_ShapeAtom_sequence2 = (Core.FieldName "sequence2")

_ShapeAtom_period = (Core.FieldName "period")

data ShapeAtom_Sequence = 
  ShapeAtom_Sequence {
    shapeAtom_SequenceNodeConstraint :: NodeConstraint,
    shapeAtom_SequenceShapeOrRef :: (Maybe ShapeOrRef)}
  deriving (Eq, Ord, Read, Show)

_ShapeAtom_Sequence = (Core.Name "hydra/langs/shex/syntax.ShapeAtom.Sequence")

_ShapeAtom_Sequence_nodeConstraint = (Core.FieldName "nodeConstraint")

_ShapeAtom_Sequence_shapeOrRef = (Core.FieldName "shapeOrRef")

data InlineShapeAtom = 
  InlineShapeAtomSequence InlineShapeAtom_Sequence |
  InlineShapeAtomSequence2 InlineShapeAtom_Sequence2 |
  InlineShapeAtomSequence3 ShapeExpression |
  InlineShapeAtomPeriod 
  deriving (Eq, Ord, Read, Show)

_InlineShapeAtom = (Core.Name "hydra/langs/shex/syntax.InlineShapeAtom")

_InlineShapeAtom_sequence = (Core.FieldName "sequence")

_InlineShapeAtom_sequence2 = (Core.FieldName "sequence2")

_InlineShapeAtom_sequence3 = (Core.FieldName "sequence3")

_InlineShapeAtom_period = (Core.FieldName "period")

data InlineShapeAtom_Sequence = 
  InlineShapeAtom_Sequence {
    inlineShapeAtom_SequenceNodeConstraint :: NodeConstraint,
    inlineShapeAtom_SequenceInlineShapeOrRef :: (Maybe InlineShapeOrRef)}
  deriving (Eq, Ord, Read, Show)

_InlineShapeAtom_Sequence = (Core.Name "hydra/langs/shex/syntax.InlineShapeAtom.Sequence")

_InlineShapeAtom_Sequence_nodeConstraint = (Core.FieldName "nodeConstraint")

_InlineShapeAtom_Sequence_inlineShapeOrRef = (Core.FieldName "inlineShapeOrRef")

data InlineShapeAtom_Sequence2 = 
  InlineShapeAtom_Sequence2 {
    inlineShapeAtom_Sequence2InlineShapeOrRef :: InlineShapeOrRef,
    inlineShapeAtom_Sequence2NodeConstraint :: (Maybe NodeConstraint)}
  deriving (Eq, Ord, Read, Show)

_InlineShapeAtom_Sequence2 = (Core.Name "hydra/langs/shex/syntax.InlineShapeAtom.Sequence2")

_InlineShapeAtom_Sequence2_inlineShapeOrRef = (Core.FieldName "inlineShapeOrRef")

_InlineShapeAtom_Sequence2_nodeConstraint = (Core.FieldName "nodeConstraint")

data ShapeOrRef = 
  ShapeOrRefShapeDefinition ShapeDefinition |
  ShapeOrRefAtpNameLn AtpNameLn |
  ShapeOrRefAtpNameNs AtpNameNs |
  ShapeOrRefSequence ShapeExprLabel
  deriving (Eq, Ord, Read, Show)

_ShapeOrRef = (Core.Name "hydra/langs/shex/syntax.ShapeOrRef")

_ShapeOrRef_shapeDefinition = (Core.FieldName "shapeDefinition")

_ShapeOrRef_atpNameLn = (Core.FieldName "atpNameLn")

_ShapeOrRef_atpNameNs = (Core.FieldName "atpNameNs")

_ShapeOrRef_sequence = (Core.FieldName "sequence")

data InlineShapeOrRef = 
  InlineShapeOrRefInlineShapeDefinition InlineShapeDefinition |
  InlineShapeOrRefAtpNameLn AtpNameLn |
  InlineShapeOrRefAtpNameNs AtpNameNs |
  InlineShapeOrRefSequence ShapeExprLabel
  deriving (Eq, Ord, Read, Show)

_InlineShapeOrRef = (Core.Name "hydra/langs/shex/syntax.InlineShapeOrRef")

_InlineShapeOrRef_inlineShapeDefinition = (Core.FieldName "inlineShapeDefinition")

_InlineShapeOrRef_atpNameLn = (Core.FieldName "atpNameLn")

_InlineShapeOrRef_atpNameNs = (Core.FieldName "atpNameNs")

_InlineShapeOrRef_sequence = (Core.FieldName "sequence")

data NodeConstraint = 
  NodeConstraintSequence [XsFacet] |
  NodeConstraintSequence2 NodeConstraint_Sequence2 |
  NodeConstraintSequence3 NodeConstraint_Sequence3 |
  NodeConstraintSequence4 NodeConstraint_Sequence4 |
  NodeConstraintSequence5 NodeConstraint_Sequence5 |
  NodeConstraintListOfXsFacet [XsFacet]
  deriving (Eq, Ord, Read, Show)

_NodeConstraint = (Core.Name "hydra/langs/shex/syntax.NodeConstraint")

_NodeConstraint_sequence = (Core.FieldName "sequence")

_NodeConstraint_sequence2 = (Core.FieldName "sequence2")

_NodeConstraint_sequence3 = (Core.FieldName "sequence3")

_NodeConstraint_sequence4 = (Core.FieldName "sequence4")

_NodeConstraint_sequence5 = (Core.FieldName "sequence5")

_NodeConstraint_listOfXsFacet = (Core.FieldName "listOfXsFacet")

data NodeConstraint_Sequence2 = 
  NodeConstraint_Sequence2 {
    nodeConstraint_Sequence2NonLiteralKind :: NonLiteralKind,
    nodeConstraint_Sequence2ListOfStringFacet :: [StringFacet]}
  deriving (Eq, Ord, Read, Show)

_NodeConstraint_Sequence2 = (Core.Name "hydra/langs/shex/syntax.NodeConstraint.Sequence2")

_NodeConstraint_Sequence2_nonLiteralKind = (Core.FieldName "nonLiteralKind")

_NodeConstraint_Sequence2_listOfStringFacet = (Core.FieldName "listOfStringFacet")

data NodeConstraint_Sequence3 = 
  NodeConstraint_Sequence3 {
    nodeConstraint_Sequence3Datatype :: Datatype,
    nodeConstraint_Sequence3ListOfXsFacet :: [XsFacet]}
  deriving (Eq, Ord, Read, Show)

_NodeConstraint_Sequence3 = (Core.Name "hydra/langs/shex/syntax.NodeConstraint.Sequence3")

_NodeConstraint_Sequence3_datatype = (Core.FieldName "datatype")

_NodeConstraint_Sequence3_listOfXsFacet = (Core.FieldName "listOfXsFacet")

data NodeConstraint_Sequence4 = 
  NodeConstraint_Sequence4 {
    nodeConstraint_Sequence4ValueSet :: ValueSet,
    nodeConstraint_Sequence4ListOfXsFacet :: [XsFacet]}
  deriving (Eq, Ord, Read, Show)

_NodeConstraint_Sequence4 = (Core.Name "hydra/langs/shex/syntax.NodeConstraint.Sequence4")

_NodeConstraint_Sequence4_valueSet = (Core.FieldName "valueSet")

_NodeConstraint_Sequence4_listOfXsFacet = (Core.FieldName "listOfXsFacet")

data NodeConstraint_Sequence5 = 
  NodeConstraint_Sequence5 {
    nodeConstraint_Sequence5ValueSet :: ValueSet,
    nodeConstraint_Sequence5ListOfXsFacet :: [XsFacet]}
  deriving (Eq, Ord, Read, Show)

_NodeConstraint_Sequence5 = (Core.Name "hydra/langs/shex/syntax.NodeConstraint.Sequence5")

_NodeConstraint_Sequence5_valueSet = (Core.FieldName "valueSet")

_NodeConstraint_Sequence5_listOfXsFacet = (Core.FieldName "listOfXsFacet")

data NonLiteralKind = 
  NonLiteralKindIRI  |
  NonLiteralKindBNODE  |
  NonLiteralKindNONLITERAL 
  deriving (Eq, Ord, Read, Show)

_NonLiteralKind = (Core.Name "hydra/langs/shex/syntax.NonLiteralKind")

_NonLiteralKind_iRI = (Core.FieldName "iRI")

_NonLiteralKind_bNODE = (Core.FieldName "bNODE")

_NonLiteralKind_nONLITERAL = (Core.FieldName "nONLITERAL")

data XsFacet = 
  XsFacetStringFacet StringFacet |
  XsFacetNumericFacet NumericFacet
  deriving (Eq, Ord, Read, Show)

_XsFacet = (Core.Name "hydra/langs/shex/syntax.XsFacet")

_XsFacet_stringFacet = (Core.FieldName "stringFacet")

_XsFacet_numericFacet = (Core.FieldName "numericFacet")

data StringFacet = 
  StringFacetSequence StringFacet_Sequence |
  StringFacetRegexp Regexp
  deriving (Eq, Ord, Read, Show)

_StringFacet = (Core.Name "hydra/langs/shex/syntax.StringFacet")

_StringFacet_sequence = (Core.FieldName "sequence")

_StringFacet_regexp = (Core.FieldName "regexp")

data StringFacet_Sequence = 
  StringFacet_Sequence {
    stringFacet_SequenceStringLength :: StringLength,
    stringFacet_SequenceInteger :: Integer_}
  deriving (Eq, Ord, Read, Show)

_StringFacet_Sequence = (Core.Name "hydra/langs/shex/syntax.StringFacet.Sequence")

_StringFacet_Sequence_stringLength = (Core.FieldName "stringLength")

_StringFacet_Sequence_integer = (Core.FieldName "integer")

data StringLength = 
  StringLengthLENGTH  |
  StringLengthMINLENGTH  |
  StringLengthMAXLENGTH 
  deriving (Eq, Ord, Read, Show)

_StringLength = (Core.Name "hydra/langs/shex/syntax.StringLength")

_StringLength_lENGTH = (Core.FieldName "lENGTH")

_StringLength_mINLENGTH = (Core.FieldName "mINLENGTH")

_StringLength_mAXLENGTH = (Core.FieldName "mAXLENGTH")

data NumericFacet = 
  NumericFacetSequence NumericFacet_Sequence |
  NumericFacetSequence2 NumericFacet_Sequence2
  deriving (Eq, Ord, Read, Show)

_NumericFacet = (Core.Name "hydra/langs/shex/syntax.NumericFacet")

_NumericFacet_sequence = (Core.FieldName "sequence")

_NumericFacet_sequence2 = (Core.FieldName "sequence2")

data NumericFacet_Sequence = 
  NumericFacet_Sequence {
    numericFacet_SequenceNumericRange :: NumericRange,
    numericFacet_SequenceNumericLiteral :: NumericLiteral}
  deriving (Eq, Ord, Read, Show)

_NumericFacet_Sequence = (Core.Name "hydra/langs/shex/syntax.NumericFacet.Sequence")

_NumericFacet_Sequence_numericRange = (Core.FieldName "numericRange")

_NumericFacet_Sequence_numericLiteral = (Core.FieldName "numericLiteral")

data NumericFacet_Sequence2 = 
  NumericFacet_Sequence2 {
    numericFacet_Sequence2NumericLength :: NumericLength,
    numericFacet_Sequence2Integer :: Integer_}
  deriving (Eq, Ord, Read, Show)

_NumericFacet_Sequence2 = (Core.Name "hydra/langs/shex/syntax.NumericFacet.Sequence2")

_NumericFacet_Sequence2_numericLength = (Core.FieldName "numericLength")

_NumericFacet_Sequence2_integer = (Core.FieldName "integer")

data NumericRange = 
  NumericRangeMININCLUSIVE  |
  NumericRangeMINEXCLUSIVE  |
  NumericRangeMAXINCLUSIVE  |
  NumericRangeMAXEXCLUSIVE 
  deriving (Eq, Ord, Read, Show)

_NumericRange = (Core.Name "hydra/langs/shex/syntax.NumericRange")

_NumericRange_mININCLUSIVE = (Core.FieldName "mININCLUSIVE")

_NumericRange_mINEXCLUSIVE = (Core.FieldName "mINEXCLUSIVE")

_NumericRange_mAXINCLUSIVE = (Core.FieldName "mAXINCLUSIVE")

_NumericRange_mAXEXCLUSIVE = (Core.FieldName "mAXEXCLUSIVE")

data NumericLength = 
  NumericLengthTOTALDIGITS  |
  NumericLengthFRACTIONDIGITS 
  deriving (Eq, Ord, Read, Show)

_NumericLength = (Core.Name "hydra/langs/shex/syntax.NumericLength")

_NumericLength_tOTALDIGITS = (Core.FieldName "tOTALDIGITS")

_NumericLength_fRACTIONDIGITS = (Core.FieldName "fRACTIONDIGITS")

data ShapeDefinition = 
  ShapeDefinition {
    shapeDefinitionListOfAlts :: [ShapeDefinition_ListOfAlts_Elmt],
    shapeDefinitionTripleExpression :: (Maybe TripleExpression),
    shapeDefinitionListOfAnnotation :: [Annotation],
    shapeDefinitionSemanticActions :: SemanticActions}
  deriving (Eq, Ord, Read, Show)

_ShapeDefinition = (Core.Name "hydra/langs/shex/syntax.ShapeDefinition")

_ShapeDefinition_listOfAlts = (Core.FieldName "listOfAlts")

_ShapeDefinition_tripleExpression = (Core.FieldName "tripleExpression")

_ShapeDefinition_listOfAnnotation = (Core.FieldName "listOfAnnotation")

_ShapeDefinition_semanticActions = (Core.FieldName "semanticActions")

data ShapeDefinition_ListOfAlts_Elmt = 
  ShapeDefinition_ListOfAlts_ElmtIncludeSet IncludeSet |
  ShapeDefinition_ListOfAlts_ElmtExtraPropertySet ExtraPropertySet |
  ShapeDefinition_ListOfAlts_ElmtCLOSED 
  deriving (Eq, Ord, Read, Show)

_ShapeDefinition_ListOfAlts_Elmt = (Core.Name "hydra/langs/shex/syntax.ShapeDefinition.ListOfAlts.Elmt")

_ShapeDefinition_ListOfAlts_Elmt_includeSet = (Core.FieldName "includeSet")

_ShapeDefinition_ListOfAlts_Elmt_extraPropertySet = (Core.FieldName "extraPropertySet")

_ShapeDefinition_ListOfAlts_Elmt_cLOSED = (Core.FieldName "cLOSED")

data InlineShapeDefinition = 
  InlineShapeDefinition {
    inlineShapeDefinitionListOfAlts :: [InlineShapeDefinition_ListOfAlts_Elmt],
    inlineShapeDefinitionTripleExpression :: (Maybe TripleExpression)}
  deriving (Eq, Ord, Read, Show)

_InlineShapeDefinition = (Core.Name "hydra/langs/shex/syntax.InlineShapeDefinition")

_InlineShapeDefinition_listOfAlts = (Core.FieldName "listOfAlts")

_InlineShapeDefinition_tripleExpression = (Core.FieldName "tripleExpression")

data InlineShapeDefinition_ListOfAlts_Elmt = 
  InlineShapeDefinition_ListOfAlts_ElmtIncludeSet IncludeSet |
  InlineShapeDefinition_ListOfAlts_ElmtExtraPropertySet ExtraPropertySet |
  InlineShapeDefinition_ListOfAlts_ElmtCLOSED 
  deriving (Eq, Ord, Read, Show)

_InlineShapeDefinition_ListOfAlts_Elmt = (Core.Name "hydra/langs/shex/syntax.InlineShapeDefinition.ListOfAlts.Elmt")

_InlineShapeDefinition_ListOfAlts_Elmt_includeSet = (Core.FieldName "includeSet")

_InlineShapeDefinition_ListOfAlts_Elmt_extraPropertySet = (Core.FieldName "extraPropertySet")

_InlineShapeDefinition_ListOfAlts_Elmt_cLOSED = (Core.FieldName "cLOSED")

newtype ExtraPropertySet = 
  ExtraPropertySet {
    unExtraPropertySet :: [Predicate]}
  deriving (Eq, Ord, Read, Show)

_ExtraPropertySet = (Core.Name "hydra/langs/shex/syntax.ExtraPropertySet")

newtype TripleExpression = 
  TripleExpression {
    unTripleExpression :: OneOfTripleExpr}
  deriving (Eq, Ord, Read, Show)

_TripleExpression = (Core.Name "hydra/langs/shex/syntax.TripleExpression")

data OneOfTripleExpr = 
  OneOfTripleExprGroupTripleExpr GroupTripleExpr |
  OneOfTripleExprMultiElementOneOf MultiElementOneOf
  deriving (Eq, Ord, Read, Show)

_OneOfTripleExpr = (Core.Name "hydra/langs/shex/syntax.OneOfTripleExpr")

_OneOfTripleExpr_groupTripleExpr = (Core.FieldName "groupTripleExpr")

_OneOfTripleExpr_multiElementOneOf = (Core.FieldName "multiElementOneOf")

data MultiElementOneOf = 
  MultiElementOneOf {
    multiElementOneOfGroupTripleExpr :: GroupTripleExpr,
    multiElementOneOfListOfSequence :: [GroupTripleExpr]}
  deriving (Eq, Ord, Read, Show)

_MultiElementOneOf = (Core.Name "hydra/langs/shex/syntax.MultiElementOneOf")

_MultiElementOneOf_groupTripleExpr = (Core.FieldName "groupTripleExpr")

_MultiElementOneOf_listOfSequence = (Core.FieldName "listOfSequence")

data InnerTripleExpr = 
  InnerTripleExprMultiElementGroup MultiElementGroup |
  InnerTripleExprMultiElementOneOf MultiElementOneOf
  deriving (Eq, Ord, Read, Show)

_InnerTripleExpr = (Core.Name "hydra/langs/shex/syntax.InnerTripleExpr")

_InnerTripleExpr_multiElementGroup = (Core.FieldName "multiElementGroup")

_InnerTripleExpr_multiElementOneOf = (Core.FieldName "multiElementOneOf")

data GroupTripleExpr = 
  GroupTripleExprSingleElementGroup SingleElementGroup |
  GroupTripleExprMultiElementGroup MultiElementGroup
  deriving (Eq, Ord, Read, Show)

_GroupTripleExpr = (Core.Name "hydra/langs/shex/syntax.GroupTripleExpr")

_GroupTripleExpr_singleElementGroup = (Core.FieldName "singleElementGroup")

_GroupTripleExpr_multiElementGroup = (Core.FieldName "multiElementGroup")

data SingleElementGroup = 
  SingleElementGroup {
    singleElementGroupUnaryTripleExpr :: UnaryTripleExpr,
    singleElementGroupSemi :: (Maybe ())}
  deriving (Eq, Ord, Read, Show)

_SingleElementGroup = (Core.Name "hydra/langs/shex/syntax.SingleElementGroup")

_SingleElementGroup_unaryTripleExpr = (Core.FieldName "unaryTripleExpr")

_SingleElementGroup_semi = (Core.FieldName "semi")

data MultiElementGroup = 
  MultiElementGroup {
    multiElementGroupUnaryTripleExpr :: UnaryTripleExpr,
    multiElementGroupListOfSequence :: [UnaryTripleExpr],
    multiElementGroupSemi :: (Maybe ())}
  deriving (Eq, Ord, Read, Show)

_MultiElementGroup = (Core.Name "hydra/langs/shex/syntax.MultiElementGroup")

_MultiElementGroup_unaryTripleExpr = (Core.FieldName "unaryTripleExpr")

_MultiElementGroup_listOfSequence = (Core.FieldName "listOfSequence")

_MultiElementGroup_semi = (Core.FieldName "semi")

data UnaryTripleExpr = 
  UnaryTripleExprSequence UnaryTripleExpr_Sequence |
  UnaryTripleExprInclude Include
  deriving (Eq, Ord, Read, Show)

_UnaryTripleExpr = (Core.Name "hydra/langs/shex/syntax.UnaryTripleExpr")

_UnaryTripleExpr_sequence = (Core.FieldName "sequence")

_UnaryTripleExpr_include = (Core.FieldName "include")

data UnaryTripleExpr_Sequence = 
  UnaryTripleExpr_Sequence {
    unaryTripleExpr_SequenceSequence :: (Maybe TripleExprLabel),
    unaryTripleExpr_SequenceAlts :: UnaryTripleExpr_Sequence_Alts}
  deriving (Eq, Ord, Read, Show)

_UnaryTripleExpr_Sequence = (Core.Name "hydra/langs/shex/syntax.UnaryTripleExpr.Sequence")

_UnaryTripleExpr_Sequence_sequence = (Core.FieldName "sequence")

_UnaryTripleExpr_Sequence_alts = (Core.FieldName "alts")

data UnaryTripleExpr_Sequence_Alts = 
  UnaryTripleExpr_Sequence_AltsTripleConstraint TripleConstraint |
  UnaryTripleExpr_Sequence_AltsBracketedTripleExpr BracketedTripleExpr
  deriving (Eq, Ord, Read, Show)

_UnaryTripleExpr_Sequence_Alts = (Core.Name "hydra/langs/shex/syntax.UnaryTripleExpr.Sequence.Alts")

_UnaryTripleExpr_Sequence_Alts_tripleConstraint = (Core.FieldName "tripleConstraint")

_UnaryTripleExpr_Sequence_Alts_bracketedTripleExpr = (Core.FieldName "bracketedTripleExpr")

data BracketedTripleExpr = 
  BracketedTripleExpr {
    bracketedTripleExprInnerTripleExpr :: InnerTripleExpr,
    bracketedTripleExprCardinality :: (Maybe Cardinality),
    bracketedTripleExprListOfAnnotation :: [Annotation],
    bracketedTripleExprSemanticActions :: SemanticActions}
  deriving (Eq, Ord, Read, Show)

_BracketedTripleExpr = (Core.Name "hydra/langs/shex/syntax.BracketedTripleExpr")

_BracketedTripleExpr_innerTripleExpr = (Core.FieldName "innerTripleExpr")

_BracketedTripleExpr_cardinality = (Core.FieldName "cardinality")

_BracketedTripleExpr_listOfAnnotation = (Core.FieldName "listOfAnnotation")

_BracketedTripleExpr_semanticActions = (Core.FieldName "semanticActions")

data TripleConstraint = 
  TripleConstraint {
    tripleConstraintSenseFlags :: (Maybe SenseFlags),
    tripleConstraintPredicate :: Predicate,
    tripleConstraintInlineShapeExpression :: InlineShapeExpression,
    tripleConstraintCardinality :: (Maybe Cardinality),
    tripleConstraintListOfAnnotation :: [Annotation],
    tripleConstraintSemanticActions :: SemanticActions}
  deriving (Eq, Ord, Read, Show)

_TripleConstraint = (Core.Name "hydra/langs/shex/syntax.TripleConstraint")

_TripleConstraint_senseFlags = (Core.FieldName "senseFlags")

_TripleConstraint_predicate = (Core.FieldName "predicate")

_TripleConstraint_inlineShapeExpression = (Core.FieldName "inlineShapeExpression")

_TripleConstraint_cardinality = (Core.FieldName "cardinality")

_TripleConstraint_listOfAnnotation = (Core.FieldName "listOfAnnotation")

_TripleConstraint_semanticActions = (Core.FieldName "semanticActions")

data Cardinality = 
  CardinalityAst  |
  CardinalityPlus  |
  CardinalityQuest  |
  CardinalityRepeatRange RepeatRange
  deriving (Eq, Ord, Read, Show)

_Cardinality = (Core.Name "hydra/langs/shex/syntax.Cardinality")

_Cardinality_ast = (Core.FieldName "ast")

_Cardinality_plus = (Core.FieldName "plus")

_Cardinality_quest = (Core.FieldName "quest")

_Cardinality_repeatRange = (Core.FieldName "repeatRange")

data SenseFlags = 
  SenseFlags {}
  deriving (Eq, Ord, Read, Show)

_SenseFlags = (Core.Name "hydra/langs/shex/syntax.SenseFlags")

newtype ValueSet = 
  ValueSet {
    unValueSet :: [ValueSetValue]}
  deriving (Eq, Ord, Read, Show)

_ValueSet = (Core.Name "hydra/langs/shex/syntax.ValueSet")

data ValueSetValue = 
  ValueSetValueIriRange IriRange |
  ValueSetValueLiteral Literal
  deriving (Eq, Ord, Read, Show)

_ValueSetValue = (Core.Name "hydra/langs/shex/syntax.ValueSetValue")

_ValueSetValue_iriRange = (Core.FieldName "iriRange")

_ValueSetValue_literal = (Core.FieldName "literal")

data IriRange = 
  IriRangeSequence IriRange_Sequence |
  IriRangeSequence2 [Exclusion]
  deriving (Eq, Ord, Read, Show)

_IriRange = (Core.Name "hydra/langs/shex/syntax.IriRange")

_IriRange_sequence = (Core.FieldName "sequence")

_IriRange_sequence2 = (Core.FieldName "sequence2")

data IriRange_Sequence = 
  IriRange_Sequence {
    iriRange_SequenceIri :: Iri,
    iriRange_SequenceSequence :: (Maybe [Exclusion])}
  deriving (Eq, Ord, Read, Show)

_IriRange_Sequence = (Core.Name "hydra/langs/shex/syntax.IriRange.Sequence")

_IriRange_Sequence_iri = (Core.FieldName "iri")

_IriRange_Sequence_sequence = (Core.FieldName "sequence")

newtype Exclusion = 
  Exclusion {
    unExclusion :: Iri}
  deriving (Eq, Ord, Read, Show)

_Exclusion = (Core.Name "hydra/langs/shex/syntax.Exclusion")

newtype Include = 
  Include {
    unInclude :: TripleExprLabel}
  deriving (Eq, Ord, Read, Show)

_Include = (Core.Name "hydra/langs/shex/syntax.Include")

data Annotation = 
  Annotation {
    annotationPredicate :: Predicate,
    annotationAlts :: Annotation_Alts}
  deriving (Eq, Ord, Read, Show)

_Annotation = (Core.Name "hydra/langs/shex/syntax.Annotation")

_Annotation_predicate = (Core.FieldName "predicate")

_Annotation_alts = (Core.FieldName "alts")

data Annotation_Alts = 
  Annotation_AltsIri Iri |
  Annotation_AltsLiteral Literal
  deriving (Eq, Ord, Read, Show)

_Annotation_Alts = (Core.Name "hydra/langs/shex/syntax.Annotation.Alts")

_Annotation_Alts_iri = (Core.FieldName "iri")

_Annotation_Alts_literal = (Core.FieldName "literal")

newtype SemanticActions = 
  SemanticActions {
    unSemanticActions :: [CodeDecl]}
  deriving (Eq, Ord, Read, Show)

_SemanticActions = (Core.Name "hydra/langs/shex/syntax.SemanticActions")

data CodeDecl = 
  CodeDecl {
    codeDeclIri :: Iri,
    codeDeclAlts :: CodeDecl_Alts}
  deriving (Eq, Ord, Read, Show)

_CodeDecl = (Core.Name "hydra/langs/shex/syntax.CodeDecl")

_CodeDecl_iri = (Core.FieldName "iri")

_CodeDecl_alts = (Core.FieldName "alts")

data CodeDecl_Alts = 
  CodeDecl_AltsCode Code |
  CodeDecl_AltsPercnt 
  deriving (Eq, Ord, Read, Show)

_CodeDecl_Alts = (Core.Name "hydra/langs/shex/syntax.CodeDecl.Alts")

_CodeDecl_Alts_code = (Core.FieldName "code")

_CodeDecl_Alts_percnt = (Core.FieldName "percnt")

data Literal = 
  LiteralRdfLiteral RdfLiteral |
  LiteralNumericLiteral NumericLiteral |
  LiteralBooleanLiteral BooleanLiteral
  deriving (Eq, Ord, Read, Show)

_Literal = (Core.Name "hydra/langs/shex/syntax.Literal")

_Literal_rdfLiteral = (Core.FieldName "rdfLiteral")

_Literal_numericLiteral = (Core.FieldName "numericLiteral")

_Literal_booleanLiteral = (Core.FieldName "booleanLiteral")

data Predicate = 
  PredicateIri Iri |
  PredicateRdfType RdfType
  deriving (Eq, Ord, Read, Show)

_Predicate = (Core.Name "hydra/langs/shex/syntax.Predicate")

_Predicate_iri = (Core.FieldName "iri")

_Predicate_rdfType = (Core.FieldName "rdfType")

newtype Datatype = 
  Datatype {
    unDatatype :: Iri}
  deriving (Eq, Ord, Read, Show)

_Datatype = (Core.Name "hydra/langs/shex/syntax.Datatype")

data ShapeExprLabel = 
  ShapeExprLabelIri Iri |
  ShapeExprLabelBlankNode BlankNode
  deriving (Eq, Ord, Read, Show)

_ShapeExprLabel = (Core.Name "hydra/langs/shex/syntax.ShapeExprLabel")

_ShapeExprLabel_iri = (Core.FieldName "iri")

_ShapeExprLabel_blankNode = (Core.FieldName "blankNode")

data TripleExprLabel = 
  TripleExprLabelIri Iri |
  TripleExprLabelBlankNode BlankNode
  deriving (Eq, Ord, Read, Show)

_TripleExprLabel = (Core.Name "hydra/langs/shex/syntax.TripleExprLabel")

_TripleExprLabel_iri = (Core.FieldName "iri")

_TripleExprLabel_blankNode = (Core.FieldName "blankNode")

data NumericLiteral = 
  NumericLiteralInteger Integer_ |
  NumericLiteralDecimal Decimal |
  NumericLiteralDouble Double_
  deriving (Eq, Ord, Read, Show)

_NumericLiteral = (Core.Name "hydra/langs/shex/syntax.NumericLiteral")

_NumericLiteral_integer = (Core.FieldName "integer")

_NumericLiteral_decimal = (Core.FieldName "decimal")

_NumericLiteral_double = (Core.FieldName "double")

data RdfLiteral = 
  RdfLiteral {
    rdfLiteralString :: String_,
    rdfLiteralAlts :: (Maybe RdfLiteral_Alts_Option)}
  deriving (Eq, Ord, Read, Show)

_RdfLiteral = (Core.Name "hydra/langs/shex/syntax.RdfLiteral")

_RdfLiteral_string = (Core.FieldName "string")

_RdfLiteral_alts = (Core.FieldName "alts")

data RdfLiteral_Alts_Option = 
  RdfLiteral_Alts_OptionLangTag LangTag |
  RdfLiteral_Alts_OptionSequence Datatype
  deriving (Eq, Ord, Read, Show)

_RdfLiteral_Alts_Option = (Core.Name "hydra/langs/shex/syntax.RdfLiteral.Alts.Option")

_RdfLiteral_Alts_Option_langTag = (Core.FieldName "langTag")

_RdfLiteral_Alts_Option_sequence = (Core.FieldName "sequence")

data BooleanLiteral = 
  BooleanLiteralTrue  |
  BooleanLiteralFalse 
  deriving (Eq, Ord, Read, Show)

_BooleanLiteral = (Core.Name "hydra/langs/shex/syntax.BooleanLiteral")

_BooleanLiteral_true = (Core.FieldName "true")

_BooleanLiteral_false = (Core.FieldName "false")

data String_ = 
  StringStringLiteral1 StringLiteral1 |
  StringStringLiteralLong1 StringLiteralLong1 |
  StringStringLiteral2 StringLiteral2 |
  StringStringLiteralLong2 StringLiteralLong2
  deriving (Eq, Ord, Read, Show)

_String = (Core.Name "hydra/langs/shex/syntax.String")

_String_stringLiteral1 = (Core.FieldName "stringLiteral1")

_String_stringLiteralLong1 = (Core.FieldName "stringLiteralLong1")

_String_stringLiteral2 = (Core.FieldName "stringLiteral2")

_String_stringLiteralLong2 = (Core.FieldName "stringLiteralLong2")

data Iri = 
  IriIriRef IriRef |
  IriPrefixedName PrefixedName
  deriving (Eq, Ord, Read, Show)

_Iri = (Core.Name "hydra/langs/shex/syntax.Iri")

_Iri_iriRef = (Core.FieldName "iriRef")

_Iri_prefixedName = (Core.FieldName "prefixedName")

data PrefixedName = 
  PrefixedNamePnameLn PnameLn |
  PrefixedNamePnameNs PnameNs
  deriving (Eq, Ord, Read, Show)

_PrefixedName = (Core.Name "hydra/langs/shex/syntax.PrefixedName")

_PrefixedName_pnameLn = (Core.FieldName "pnameLn")

_PrefixedName_pnameNs = (Core.FieldName "pnameNs")

newtype BlankNode = 
  BlankNode {
    unBlankNode :: BlankNodeLabel}
  deriving (Eq, Ord, Read, Show)

_BlankNode = (Core.Name "hydra/langs/shex/syntax.BlankNode")

newtype IncludeSet = 
  IncludeSet {
    unIncludeSet :: [ShapeExprLabel]}
  deriving (Eq, Ord, Read, Show)

_IncludeSet = (Core.Name "hydra/langs/shex/syntax.IncludeSet")

newtype Code = 
  Code {
    unCode :: [Code_Elmt]}
  deriving (Eq, Ord, Read, Show)

_Code = (Core.Name "hydra/langs/shex/syntax.Code")

data Code_Elmt = 
  Code_ElmtRegex String |
  Code_ElmtSequence String |
  Code_ElmtUchar Uchar
  deriving (Eq, Ord, Read, Show)

_Code_Elmt = (Core.Name "hydra/langs/shex/syntax.Code.Elmt")

_Code_Elmt_regex = (Core.FieldName "regex")

_Code_Elmt_sequence = (Core.FieldName "sequence")

_Code_Elmt_uchar = (Core.FieldName "uchar")

data RepeatRange = 
  RepeatRange {
    repeatRangeInteger :: Integer_,
    repeatRangeSequence :: (Maybe (Maybe (Maybe RepeatRange_Sequence_Option_Option_Option)))}
  deriving (Eq, Ord, Read, Show)

_RepeatRange = (Core.Name "hydra/langs/shex/syntax.RepeatRange")

_RepeatRange_integer = (Core.FieldName "integer")

_RepeatRange_sequence = (Core.FieldName "sequence")

data RepeatRange_Sequence_Option_Option_Option = 
  RepeatRange_Sequence_Option_Option_OptionInteger Integer_ |
  RepeatRange_Sequence_Option_Option_OptionAst 
  deriving (Eq, Ord, Read, Show)

_RepeatRange_Sequence_Option_Option_Option = (Core.Name "hydra/langs/shex/syntax.RepeatRange.Sequence.Option.Option.Option")

_RepeatRange_Sequence_Option_Option_Option_integer = (Core.FieldName "integer")

_RepeatRange_Sequence_Option_Option_Option_ast = (Core.FieldName "ast")

data RdfType = 
  RdfType {}
  deriving (Eq, Ord, Read, Show)

_RdfType = (Core.Name "hydra/langs/shex/syntax.RdfType")

newtype IriRef = 
  IriRef {
    unIriRef :: [IriRef_Elmt]}
  deriving (Eq, Ord, Read, Show)

_IriRef = (Core.Name "hydra/langs/shex/syntax.IriRef")

data IriRef_Elmt = 
  IriRef_ElmtRegex String |
  IriRef_ElmtUchar Uchar
  deriving (Eq, Ord, Read, Show)

_IriRef_Elmt = (Core.Name "hydra/langs/shex/syntax.IriRef.Elmt")

_IriRef_Elmt_regex = (Core.FieldName "regex")

_IriRef_Elmt_uchar = (Core.FieldName "uchar")

newtype PnameNs = 
  PnameNs {
    unPnameNs :: (Maybe PnPrefix)}
  deriving (Eq, Ord, Read, Show)

_PnameNs = (Core.Name "hydra/langs/shex/syntax.PnameNs")

data PnameLn = 
  PnameLn {
    pnameLnPnameNs :: PnameNs,
    pnameLnPnLocal :: PnLocal}
  deriving (Eq, Ord, Read, Show)

_PnameLn = (Core.Name "hydra/langs/shex/syntax.PnameLn")

_PnameLn_pnameNs = (Core.FieldName "pnameNs")

_PnameLn_pnLocal = (Core.FieldName "pnLocal")

newtype AtpNameNs = 
  AtpNameNs {
    unAtpNameNs :: (Maybe PnPrefix)}
  deriving (Eq, Ord, Read, Show)

_AtpNameNs = (Core.Name "hydra/langs/shex/syntax.AtpNameNs")

data AtpNameLn = 
  AtpNameLn {
    atpNameLnPnameNs :: PnameNs,
    atpNameLnPnLocal :: PnLocal}
  deriving (Eq, Ord, Read, Show)

_AtpNameLn = (Core.Name "hydra/langs/shex/syntax.AtpNameLn")

_AtpNameLn_pnameNs = (Core.FieldName "pnameNs")

_AtpNameLn_pnLocal = (Core.FieldName "pnLocal")

data Regexp = 
  Regexp {
    regexpListOfAlts :: [Regexp_ListOfAlts_Elmt],
    regexpListOfRegex :: [String]}
  deriving (Eq, Ord, Read, Show)

_Regexp = (Core.Name "hydra/langs/shex/syntax.Regexp")

_Regexp_listOfAlts = (Core.FieldName "listOfAlts")

_Regexp_listOfRegex = (Core.FieldName "listOfRegex")

data Regexp_ListOfAlts_Elmt = 
  Regexp_ListOfAlts_ElmtRegex String |
  Regexp_ListOfAlts_ElmtSequence String |
  Regexp_ListOfAlts_ElmtUchar Uchar
  deriving (Eq, Ord, Read, Show)

_Regexp_ListOfAlts_Elmt = (Core.Name "hydra/langs/shex/syntax.Regexp.ListOfAlts.Elmt")

_Regexp_ListOfAlts_Elmt_regex = (Core.FieldName "regex")

_Regexp_ListOfAlts_Elmt_sequence = (Core.FieldName "sequence")

_Regexp_ListOfAlts_Elmt_uchar = (Core.FieldName "uchar")

data BlankNodeLabel = 
  BlankNodeLabel {
    blankNodeLabelAlts :: BlankNodeLabel_Alts,
    blankNodeLabelListOfAlts :: (Maybe [BlankNodeLabel_ListOfAlts_Option_Elmt]),
    blankNodeLabelPnChars :: PnChars}
  deriving (Eq, Ord, Read, Show)

_BlankNodeLabel = (Core.Name "hydra/langs/shex/syntax.BlankNodeLabel")

_BlankNodeLabel_alts = (Core.FieldName "alts")

_BlankNodeLabel_listOfAlts = (Core.FieldName "listOfAlts")

_BlankNodeLabel_pnChars = (Core.FieldName "pnChars")

data BlankNodeLabel_Alts = 
  BlankNodeLabel_AltsPnCharsU PnCharsU |
  BlankNodeLabel_AltsRegex String
  deriving (Eq, Ord, Read, Show)

_BlankNodeLabel_Alts = (Core.Name "hydra/langs/shex/syntax.BlankNodeLabel.Alts")

_BlankNodeLabel_Alts_pnCharsU = (Core.FieldName "pnCharsU")

_BlankNodeLabel_Alts_regex = (Core.FieldName "regex")

data BlankNodeLabel_ListOfAlts_Option_Elmt = 
  BlankNodeLabel_ListOfAlts_Option_ElmtPnChars PnChars |
  BlankNodeLabel_ListOfAlts_Option_ElmtPeriod 
  deriving (Eq, Ord, Read, Show)

_BlankNodeLabel_ListOfAlts_Option_Elmt = (Core.Name "hydra/langs/shex/syntax.BlankNodeLabel.ListOfAlts.Option.Elmt")

_BlankNodeLabel_ListOfAlts_Option_Elmt_pnChars = (Core.FieldName "pnChars")

_BlankNodeLabel_ListOfAlts_Option_Elmt_period = (Core.FieldName "period")

newtype LangTag = 
  LangTag {
    unLangTag :: String}
  deriving (Eq, Ord, Read, Show)

_LangTag = (Core.Name "hydra/langs/shex/syntax.LangTag")

newtype Integer_ = 
  Integer_ {
    unInteger :: String}
  deriving (Eq, Ord, Read, Show)

_Integer = (Core.Name "hydra/langs/shex/syntax.Integer")

newtype Decimal = 
  Decimal {
    unDecimal :: String}
  deriving (Eq, Ord, Read, Show)

_Decimal = (Core.Name "hydra/langs/shex/syntax.Decimal")

newtype Double_ = 
  Double_ {
    unDouble :: String}
  deriving (Eq, Ord, Read, Show)

_Double = (Core.Name "hydra/langs/shex/syntax.Double")

newtype StringLiteral1 = 
  StringLiteral1 {
    unStringLiteral1 :: [StringLiteral1_Elmt]}
  deriving (Eq, Ord, Read, Show)

_StringLiteral1 = (Core.Name "hydra/langs/shex/syntax.StringLiteral1")

data StringLiteral1_Elmt = 
  StringLiteral1_ElmtRegex String |
  StringLiteral1_ElmtEchar Echar |
  StringLiteral1_ElmtUchar Uchar
  deriving (Eq, Ord, Read, Show)

_StringLiteral1_Elmt = (Core.Name "hydra/langs/shex/syntax.StringLiteral1.Elmt")

_StringLiteral1_Elmt_regex = (Core.FieldName "regex")

_StringLiteral1_Elmt_echar = (Core.FieldName "echar")

_StringLiteral1_Elmt_uchar = (Core.FieldName "uchar")

newtype StringLiteral2 = 
  StringLiteral2 {
    unStringLiteral2 :: [StringLiteral2_Elmt]}
  deriving (Eq, Ord, Read, Show)

_StringLiteral2 = (Core.Name "hydra/langs/shex/syntax.StringLiteral2")

data StringLiteral2_Elmt = 
  StringLiteral2_ElmtRegex String |
  StringLiteral2_ElmtEchar Echar |
  StringLiteral2_ElmtUchar Uchar
  deriving (Eq, Ord, Read, Show)

_StringLiteral2_Elmt = (Core.Name "hydra/langs/shex/syntax.StringLiteral2.Elmt")

_StringLiteral2_Elmt_regex = (Core.FieldName "regex")

_StringLiteral2_Elmt_echar = (Core.FieldName "echar")

_StringLiteral2_Elmt_uchar = (Core.FieldName "uchar")

newtype StringLiteralLong1 = 
  StringLiteralLong1 {
    unStringLiteralLong1 :: [StringLiteralLong1_Elmt]}
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong1 = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong1")

data StringLiteralLong1_Elmt = 
  StringLiteralLong1_ElmtSequence StringLiteralLong1_Elmt_Sequence |
  StringLiteralLong1_ElmtEchar Echar |
  StringLiteralLong1_ElmtUchar Uchar
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong1_Elmt = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong1.Elmt")

_StringLiteralLong1_Elmt_sequence = (Core.FieldName "sequence")

_StringLiteralLong1_Elmt_echar = (Core.FieldName "echar")

_StringLiteralLong1_Elmt_uchar = (Core.FieldName "uchar")

data StringLiteralLong1_Elmt_Sequence = 
  StringLiteralLong1_Elmt_Sequence {
    stringLiteralLong1_Elmt_SequenceAlts :: (Maybe StringLiteralLong1_Elmt_Sequence_Alts_Option),
    stringLiteralLong1_Elmt_SequenceRegex :: String}
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong1_Elmt_Sequence = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong1.Elmt.Sequence")

_StringLiteralLong1_Elmt_Sequence_alts = (Core.FieldName "alts")

_StringLiteralLong1_Elmt_Sequence_regex = (Core.FieldName "regex")

data StringLiteralLong1_Elmt_Sequence_Alts_Option = 
  StringLiteralLong1_Elmt_Sequence_Alts_OptionApos  |
  StringLiteralLong1_Elmt_Sequence_Alts_OptionSequence StringLiteralLong1_Elmt_Sequence_Alts_Option_Sequence
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong1_Elmt_Sequence_Alts_Option = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong1.Elmt.Sequence.Alts.Option")

_StringLiteralLong1_Elmt_Sequence_Alts_Option_apos = (Core.FieldName "apos")

_StringLiteralLong1_Elmt_Sequence_Alts_Option_sequence = (Core.FieldName "sequence")

data StringLiteralLong1_Elmt_Sequence_Alts_Option_Sequence = 
  StringLiteralLong1_Elmt_Sequence_Alts_Option_Sequence {}
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong1_Elmt_Sequence_Alts_Option_Sequence = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong1.Elmt.Sequence.Alts.Option.Sequence")

newtype StringLiteralLong2 = 
  StringLiteralLong2 {
    unStringLiteralLong2 :: [StringLiteralLong2_Elmt]}
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong2 = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong2")

data StringLiteralLong2_Elmt = 
  StringLiteralLong2_ElmtSequence StringLiteralLong2_Elmt_Sequence |
  StringLiteralLong2_ElmtEchar Echar |
  StringLiteralLong2_ElmtUchar Uchar
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong2_Elmt = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong2.Elmt")

_StringLiteralLong2_Elmt_sequence = (Core.FieldName "sequence")

_StringLiteralLong2_Elmt_echar = (Core.FieldName "echar")

_StringLiteralLong2_Elmt_uchar = (Core.FieldName "uchar")

data StringLiteralLong2_Elmt_Sequence = 
  StringLiteralLong2_Elmt_Sequence {
    stringLiteralLong2_Elmt_SequenceAlts :: (Maybe StringLiteralLong2_Elmt_Sequence_Alts_Option),
    stringLiteralLong2_Elmt_SequenceRegex :: String}
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong2_Elmt_Sequence = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong2.Elmt.Sequence")

_StringLiteralLong2_Elmt_Sequence_alts = (Core.FieldName "alts")

_StringLiteralLong2_Elmt_Sequence_regex = (Core.FieldName "regex")

data StringLiteralLong2_Elmt_Sequence_Alts_Option = 
  StringLiteralLong2_Elmt_Sequence_Alts_OptionQuot  |
  StringLiteralLong2_Elmt_Sequence_Alts_OptionSequence StringLiteralLong2_Elmt_Sequence_Alts_Option_Sequence
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong2_Elmt_Sequence_Alts_Option = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong2.Elmt.Sequence.Alts.Option")

_StringLiteralLong2_Elmt_Sequence_Alts_Option_quot = (Core.FieldName "quot")

_StringLiteralLong2_Elmt_Sequence_Alts_Option_sequence = (Core.FieldName "sequence")

data StringLiteralLong2_Elmt_Sequence_Alts_Option_Sequence = 
  StringLiteralLong2_Elmt_Sequence_Alts_Option_Sequence {}
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong2_Elmt_Sequence_Alts_Option_Sequence = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong2.Elmt.Sequence.Alts.Option.Sequence")

data Uchar = 
  UcharSequence Uchar_Sequence |
  UcharSequence2 Uchar_Sequence2
  deriving (Eq, Ord, Read, Show)

_Uchar = (Core.Name "hydra/langs/shex/syntax.Uchar")

_Uchar_sequence = (Core.FieldName "sequence")

_Uchar_sequence2 = (Core.FieldName "sequence2")

data Uchar_Sequence = 
  Uchar_Sequence {
    uchar_SequenceHex :: Hex,
    uchar_SequenceHex2 :: Hex,
    uchar_SequenceHex3 :: Hex,
    uchar_SequenceHex4 :: Hex}
  deriving (Eq, Ord, Read, Show)

_Uchar_Sequence = (Core.Name "hydra/langs/shex/syntax.Uchar.Sequence")

_Uchar_Sequence_hex = (Core.FieldName "hex")

_Uchar_Sequence_hex2 = (Core.FieldName "hex2")

_Uchar_Sequence_hex3 = (Core.FieldName "hex3")

_Uchar_Sequence_hex4 = (Core.FieldName "hex4")

data Uchar_Sequence2 = 
  Uchar_Sequence2 {
    uchar_Sequence2Hex :: Hex,
    uchar_Sequence2Hex2 :: Hex,
    uchar_Sequence2Hex3 :: Hex,
    uchar_Sequence2Hex4 :: Hex,
    uchar_Sequence2Hex5 :: Hex,
    uchar_Sequence2Hex6 :: Hex,
    uchar_Sequence2Hex7 :: Hex,
    uchar_Sequence2Hex8 :: Hex}
  deriving (Eq, Ord, Read, Show)

_Uchar_Sequence2 = (Core.Name "hydra/langs/shex/syntax.Uchar.Sequence2")

_Uchar_Sequence2_hex = (Core.FieldName "hex")

_Uchar_Sequence2_hex2 = (Core.FieldName "hex2")

_Uchar_Sequence2_hex3 = (Core.FieldName "hex3")

_Uchar_Sequence2_hex4 = (Core.FieldName "hex4")

_Uchar_Sequence2_hex5 = (Core.FieldName "hex5")

_Uchar_Sequence2_hex6 = (Core.FieldName "hex6")

_Uchar_Sequence2_hex7 = (Core.FieldName "hex7")

_Uchar_Sequence2_hex8 = (Core.FieldName "hex8")

newtype Echar = 
  Echar {
    unEchar :: String}
  deriving (Eq, Ord, Read, Show)

_Echar = (Core.Name "hydra/langs/shex/syntax.Echar")

data PnCharsBase = 
  PnCharsBaseRegex String |
  PnCharsBaseRegex2 String
  deriving (Eq, Ord, Read, Show)

_PnCharsBase = (Core.Name "hydra/langs/shex/syntax.PnCharsBase")

_PnCharsBase_regex = (Core.FieldName "regex")

_PnCharsBase_regex2 = (Core.FieldName "regex2")

data PnCharsU = 
  PnCharsUPnCharsBase PnCharsBase |
  PnCharsULowbar 
  deriving (Eq, Ord, Read, Show)

_PnCharsU = (Core.Name "hydra/langs/shex/syntax.PnCharsU")

_PnCharsU_pnCharsBase = (Core.FieldName "pnCharsBase")

_PnCharsU_lowbar = (Core.FieldName "lowbar")

data PnChars = 
  PnCharsPnCharsU PnCharsU |
  PnCharsMinus  |
  PnCharsRegex String
  deriving (Eq, Ord, Read, Show)

_PnChars = (Core.Name "hydra/langs/shex/syntax.PnChars")

_PnChars_pnCharsU = (Core.FieldName "pnCharsU")

_PnChars_minus = (Core.FieldName "minus")

_PnChars_regex = (Core.FieldName "regex")

data PnPrefix = 
  PnPrefix {
    pnPrefixPnCharsBase :: PnCharsBase,
    pnPrefixSequence :: (Maybe PnPrefix_Sequence_Option)}
  deriving (Eq, Ord, Read, Show)

_PnPrefix = (Core.Name "hydra/langs/shex/syntax.PnPrefix")

_PnPrefix_pnCharsBase = (Core.FieldName "pnCharsBase")

_PnPrefix_sequence = (Core.FieldName "sequence")

data PnPrefix_Sequence_Option = 
  PnPrefix_Sequence_Option {
    pnPrefix_Sequence_OptionAlts :: PnPrefix_Sequence_Option_Alts,
    pnPrefix_Sequence_OptionPnChars :: PnChars}
  deriving (Eq, Ord, Read, Show)

_PnPrefix_Sequence_Option = (Core.Name "hydra/langs/shex/syntax.PnPrefix.Sequence.Option")

_PnPrefix_Sequence_Option_alts = (Core.FieldName "alts")

_PnPrefix_Sequence_Option_pnChars = (Core.FieldName "pnChars")

data PnPrefix_Sequence_Option_Alts = 
  PnPrefix_Sequence_Option_AltsPnChars PnChars |
  PnPrefix_Sequence_Option_AltsPeriod 
  deriving (Eq, Ord, Read, Show)

_PnPrefix_Sequence_Option_Alts = (Core.Name "hydra/langs/shex/syntax.PnPrefix.Sequence.Option.Alts")

_PnPrefix_Sequence_Option_Alts_pnChars = (Core.FieldName "pnChars")

_PnPrefix_Sequence_Option_Alts_period = (Core.FieldName "period")

data PnLocal = 
  PnLocal {
    pnLocalAlts :: PnLocal_Alts,
    pnLocalSequence :: (Maybe PnLocal_Sequence_Option)}
  deriving (Eq, Ord, Read, Show)

_PnLocal = (Core.Name "hydra/langs/shex/syntax.PnLocal")

_PnLocal_alts = (Core.FieldName "alts")

_PnLocal_sequence = (Core.FieldName "sequence")

data PnLocal_Alts = 
  PnLocal_AltsPnCharsU PnCharsU |
  PnLocal_AltsColon  |
  PnLocal_AltsRegex String |
  PnLocal_AltsPlx Plx
  deriving (Eq, Ord, Read, Show)

_PnLocal_Alts = (Core.Name "hydra/langs/shex/syntax.PnLocal.Alts")

_PnLocal_Alts_pnCharsU = (Core.FieldName "pnCharsU")

_PnLocal_Alts_colon = (Core.FieldName "colon")

_PnLocal_Alts_regex = (Core.FieldName "regex")

_PnLocal_Alts_plx = (Core.FieldName "plx")

data PnLocal_Sequence_Option = 
  PnLocal_Sequence_Option {
    pnLocal_Sequence_OptionListOfAlts :: [PnLocal_Sequence_Option_ListOfAlts_Elmt],
    pnLocal_Sequence_OptionAlts :: PnLocal_Sequence_Option_Alts}
  deriving (Eq, Ord, Read, Show)

_PnLocal_Sequence_Option = (Core.Name "hydra/langs/shex/syntax.PnLocal.Sequence.Option")

_PnLocal_Sequence_Option_listOfAlts = (Core.FieldName "listOfAlts")

_PnLocal_Sequence_Option_alts = (Core.FieldName "alts")

data PnLocal_Sequence_Option_ListOfAlts_Elmt = 
  PnLocal_Sequence_Option_ListOfAlts_ElmtPnChars PnChars |
  PnLocal_Sequence_Option_ListOfAlts_ElmtPeriod  |
  PnLocal_Sequence_Option_ListOfAlts_ElmtColon  |
  PnLocal_Sequence_Option_ListOfAlts_ElmtPlx Plx
  deriving (Eq, Ord, Read, Show)

_PnLocal_Sequence_Option_ListOfAlts_Elmt = (Core.Name "hydra/langs/shex/syntax.PnLocal.Sequence.Option.ListOfAlts.Elmt")

_PnLocal_Sequence_Option_ListOfAlts_Elmt_pnChars = (Core.FieldName "pnChars")

_PnLocal_Sequence_Option_ListOfAlts_Elmt_period = (Core.FieldName "period")

_PnLocal_Sequence_Option_ListOfAlts_Elmt_colon = (Core.FieldName "colon")

_PnLocal_Sequence_Option_ListOfAlts_Elmt_plx = (Core.FieldName "plx")

data PnLocal_Sequence_Option_Alts = 
  PnLocal_Sequence_Option_AltsPnChars PnChars |
  PnLocal_Sequence_Option_AltsColon  |
  PnLocal_Sequence_Option_AltsPlx Plx
  deriving (Eq, Ord, Read, Show)

_PnLocal_Sequence_Option_Alts = (Core.Name "hydra/langs/shex/syntax.PnLocal.Sequence.Option.Alts")

_PnLocal_Sequence_Option_Alts_pnChars = (Core.FieldName "pnChars")

_PnLocal_Sequence_Option_Alts_colon = (Core.FieldName "colon")

_PnLocal_Sequence_Option_Alts_plx = (Core.FieldName "plx")

data Plx = 
  PlxPercent Percent |
  PlxPnLocalEsc PnLocalEsc
  deriving (Eq, Ord, Read, Show)

_Plx = (Core.Name "hydra/langs/shex/syntax.Plx")

_Plx_percent = (Core.FieldName "percent")

_Plx_pnLocalEsc = (Core.FieldName "pnLocalEsc")

data Percent = 
  Percent {
    percentHex :: Hex,
    percentHex2 :: Hex}
  deriving (Eq, Ord, Read, Show)

_Percent = (Core.Name "hydra/langs/shex/syntax.Percent")

_Percent_hex = (Core.FieldName "hex")

_Percent_hex2 = (Core.FieldName "hex2")

newtype Hex = 
  Hex {
    unHex :: String}
  deriving (Eq, Ord, Read, Show)

_Hex = (Core.Name "hydra/langs/shex/syntax.Hex")

newtype PnLocalEsc = 
  PnLocalEsc {
    unPnLocalEsc :: String}
  deriving (Eq, Ord, Read, Show)

_PnLocalEsc = (Core.Name "hydra/langs/shex/syntax.PnLocalEsc")