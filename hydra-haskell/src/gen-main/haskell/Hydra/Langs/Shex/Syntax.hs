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

_ShexDoc_listOfDirective = (Core.Name "listOfDirective")

_ShexDoc_sequence = (Core.Name "sequence")

_ShexDoc_prefixDecl = (Core.Name "prefixDecl")

data ShexDoc_Sequence_Option = 
  ShexDoc_Sequence_Option {
    shexDoc_Sequence_OptionAlts :: ShexDoc_Sequence_Option_Alts,
    shexDoc_Sequence_OptionListOfStatement :: [Statement]}
  deriving (Eq, Ord, Read, Show)

_ShexDoc_Sequence_Option = (Core.Name "hydra/langs/shex/syntax.ShexDoc.Sequence.Option")

_ShexDoc_Sequence_Option_alts = (Core.Name "alts")

_ShexDoc_Sequence_Option_listOfStatement = (Core.Name "listOfStatement")

data ShexDoc_Sequence_Option_Alts = 
  ShexDoc_Sequence_Option_AltsNotStartAction NotStartAction |
  ShexDoc_Sequence_Option_AltsStartActions StartActions
  deriving (Eq, Ord, Read, Show)

_ShexDoc_Sequence_Option_Alts = (Core.Name "hydra/langs/shex/syntax.ShexDoc.Sequence.Option.Alts")

_ShexDoc_Sequence_Option_Alts_notStartAction = (Core.Name "notStartAction")

_ShexDoc_Sequence_Option_Alts_startActions = (Core.Name "startActions")

data Directive = 
  DirectiveBaseDecl BaseDecl |
  DirectivePrefixDecl PrefixDecl
  deriving (Eq, Ord, Read, Show)

_Directive = (Core.Name "hydra/langs/shex/syntax.Directive")

_Directive_baseDecl = (Core.Name "baseDecl")

_Directive_prefixDecl = (Core.Name "prefixDecl")

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

_PrefixDecl_pnameNs = (Core.Name "pnameNs")

_PrefixDecl_iriRef = (Core.Name "iriRef")

data NotStartAction = 
  NotStartActionStart ShapeExpression |
  NotStartActionShapeExprDecl NotStartAction_ShapeExprDecl
  deriving (Eq, Ord, Read, Show)

_NotStartAction = (Core.Name "hydra/langs/shex/syntax.NotStartAction")

_NotStartAction_start = (Core.Name "start")

_NotStartAction_shapeExprDecl = (Core.Name "shapeExprDecl")

data NotStartAction_ShapeExprDecl = 
  NotStartAction_ShapeExprDecl {
    notStartAction_ShapeExprDeclShapeExprLabel :: ShapeExprLabel,
    notStartAction_ShapeExprDeclAlts :: NotStartAction_ShapeExprDecl_Alts}
  deriving (Eq, Ord, Read, Show)

_NotStartAction_ShapeExprDecl = (Core.Name "hydra/langs/shex/syntax.NotStartAction.ShapeExprDecl")

_NotStartAction_ShapeExprDecl_shapeExprLabel = (Core.Name "shapeExprLabel")

_NotStartAction_ShapeExprDecl_alts = (Core.Name "alts")

data NotStartAction_ShapeExprDecl_Alts = 
  NotStartAction_ShapeExprDecl_AltsShapeExpression ShapeExpression |
  NotStartAction_ShapeExprDecl_AltsEXTERNAL 
  deriving (Eq, Ord, Read, Show)

_NotStartAction_ShapeExprDecl_Alts = (Core.Name "hydra/langs/shex/syntax.NotStartAction.ShapeExprDecl.Alts")

_NotStartAction_ShapeExprDecl_Alts_shapeExpression = (Core.Name "shapeExpression")

_NotStartAction_ShapeExprDecl_Alts_eXTERNAL = (Core.Name "eXTERNAL")

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

_Statement_directive = (Core.Name "directive")

_Statement_notStartAction = (Core.Name "notStartAction")

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

_ShapeOr_shapeAnd = (Core.Name "shapeAnd")

_ShapeOr_listOfSequence = (Core.Name "listOfSequence")

data InlineShapeOr = 
  InlineShapeOr {
    inlineShapeOrShapeAnd :: ShapeAnd,
    inlineShapeOrListOfSequence :: [InlineShapeAnd]}
  deriving (Eq, Ord, Read, Show)

_InlineShapeOr = (Core.Name "hydra/langs/shex/syntax.InlineShapeOr")

_InlineShapeOr_shapeAnd = (Core.Name "shapeAnd")

_InlineShapeOr_listOfSequence = (Core.Name "listOfSequence")

data ShapeAnd = 
  ShapeAnd {
    shapeAndShapeNot :: ShapeNot,
    shapeAndListOfSequence :: [ShapeNot]}
  deriving (Eq, Ord, Read, Show)

_ShapeAnd = (Core.Name "hydra/langs/shex/syntax.ShapeAnd")

_ShapeAnd_shapeNot = (Core.Name "shapeNot")

_ShapeAnd_listOfSequence = (Core.Name "listOfSequence")

data InlineShapeAnd = 
  InlineShapeAnd {
    inlineShapeAndInlineShapeNot :: InlineShapeNot,
    inlineShapeAndListOfSequence :: [InlineShapeNot]}
  deriving (Eq, Ord, Read, Show)

_InlineShapeAnd = (Core.Name "hydra/langs/shex/syntax.InlineShapeAnd")

_InlineShapeAnd_inlineShapeNot = (Core.Name "inlineShapeNot")

_InlineShapeAnd_listOfSequence = (Core.Name "listOfSequence")

data ShapeNot = 
  ShapeNot {
    shapeNotNOT :: (Maybe ()),
    shapeNotShapeAtom :: ShapeAtom}
  deriving (Eq, Ord, Read, Show)

_ShapeNot = (Core.Name "hydra/langs/shex/syntax.ShapeNot")

_ShapeNot_nOT = (Core.Name "nOT")

_ShapeNot_shapeAtom = (Core.Name "shapeAtom")

data InlineShapeNot = 
  InlineShapeNot {
    inlineShapeNotNOT :: (Maybe ()),
    inlineShapeNotInlineShapeAtom :: InlineShapeAtom}
  deriving (Eq, Ord, Read, Show)

_InlineShapeNot = (Core.Name "hydra/langs/shex/syntax.InlineShapeNot")

_InlineShapeNot_nOT = (Core.Name "nOT")

_InlineShapeNot_inlineShapeAtom = (Core.Name "inlineShapeAtom")

data ShapeAtom = 
  ShapeAtomSequence ShapeAtom_Sequence |
  ShapeAtomShapeOrRef ShapeOrRef |
  ShapeAtomSequence2 ShapeExpression |
  ShapeAtomPeriod 
  deriving (Eq, Ord, Read, Show)

_ShapeAtom = (Core.Name "hydra/langs/shex/syntax.ShapeAtom")

_ShapeAtom_sequence = (Core.Name "sequence")

_ShapeAtom_shapeOrRef = (Core.Name "shapeOrRef")

_ShapeAtom_sequence2 = (Core.Name "sequence2")

_ShapeAtom_period = (Core.Name "period")

data ShapeAtom_Sequence = 
  ShapeAtom_Sequence {
    shapeAtom_SequenceNodeConstraint :: NodeConstraint,
    shapeAtom_SequenceShapeOrRef :: (Maybe ShapeOrRef)}
  deriving (Eq, Ord, Read, Show)

_ShapeAtom_Sequence = (Core.Name "hydra/langs/shex/syntax.ShapeAtom.Sequence")

_ShapeAtom_Sequence_nodeConstraint = (Core.Name "nodeConstraint")

_ShapeAtom_Sequence_shapeOrRef = (Core.Name "shapeOrRef")

data InlineShapeAtom = 
  InlineShapeAtomSequence InlineShapeAtom_Sequence |
  InlineShapeAtomSequence2 InlineShapeAtom_Sequence2 |
  InlineShapeAtomSequence3 ShapeExpression |
  InlineShapeAtomPeriod 
  deriving (Eq, Ord, Read, Show)

_InlineShapeAtom = (Core.Name "hydra/langs/shex/syntax.InlineShapeAtom")

_InlineShapeAtom_sequence = (Core.Name "sequence")

_InlineShapeAtom_sequence2 = (Core.Name "sequence2")

_InlineShapeAtom_sequence3 = (Core.Name "sequence3")

_InlineShapeAtom_period = (Core.Name "period")

data InlineShapeAtom_Sequence = 
  InlineShapeAtom_Sequence {
    inlineShapeAtom_SequenceNodeConstraint :: NodeConstraint,
    inlineShapeAtom_SequenceInlineShapeOrRef :: (Maybe InlineShapeOrRef)}
  deriving (Eq, Ord, Read, Show)

_InlineShapeAtom_Sequence = (Core.Name "hydra/langs/shex/syntax.InlineShapeAtom.Sequence")

_InlineShapeAtom_Sequence_nodeConstraint = (Core.Name "nodeConstraint")

_InlineShapeAtom_Sequence_inlineShapeOrRef = (Core.Name "inlineShapeOrRef")

data InlineShapeAtom_Sequence2 = 
  InlineShapeAtom_Sequence2 {
    inlineShapeAtom_Sequence2InlineShapeOrRef :: InlineShapeOrRef,
    inlineShapeAtom_Sequence2NodeConstraint :: (Maybe NodeConstraint)}
  deriving (Eq, Ord, Read, Show)

_InlineShapeAtom_Sequence2 = (Core.Name "hydra/langs/shex/syntax.InlineShapeAtom.Sequence2")

_InlineShapeAtom_Sequence2_inlineShapeOrRef = (Core.Name "inlineShapeOrRef")

_InlineShapeAtom_Sequence2_nodeConstraint = (Core.Name "nodeConstraint")

data ShapeOrRef = 
  ShapeOrRefShapeDefinition ShapeDefinition |
  ShapeOrRefAtpNameLn AtpNameLn |
  ShapeOrRefAtpNameNs AtpNameNs |
  ShapeOrRefSequence ShapeExprLabel
  deriving (Eq, Ord, Read, Show)

_ShapeOrRef = (Core.Name "hydra/langs/shex/syntax.ShapeOrRef")

_ShapeOrRef_shapeDefinition = (Core.Name "shapeDefinition")

_ShapeOrRef_atpNameLn = (Core.Name "atpNameLn")

_ShapeOrRef_atpNameNs = (Core.Name "atpNameNs")

_ShapeOrRef_sequence = (Core.Name "sequence")

data InlineShapeOrRef = 
  InlineShapeOrRefInlineShapeDefinition InlineShapeDefinition |
  InlineShapeOrRefAtpNameLn AtpNameLn |
  InlineShapeOrRefAtpNameNs AtpNameNs |
  InlineShapeOrRefSequence ShapeExprLabel
  deriving (Eq, Ord, Read, Show)

_InlineShapeOrRef = (Core.Name "hydra/langs/shex/syntax.InlineShapeOrRef")

_InlineShapeOrRef_inlineShapeDefinition = (Core.Name "inlineShapeDefinition")

_InlineShapeOrRef_atpNameLn = (Core.Name "atpNameLn")

_InlineShapeOrRef_atpNameNs = (Core.Name "atpNameNs")

_InlineShapeOrRef_sequence = (Core.Name "sequence")

data NodeConstraint = 
  NodeConstraintSequence [XsFacet] |
  NodeConstraintSequence2 NodeConstraint_Sequence2 |
  NodeConstraintSequence3 NodeConstraint_Sequence3 |
  NodeConstraintSequence4 NodeConstraint_Sequence4 |
  NodeConstraintSequence5 NodeConstraint_Sequence5 |
  NodeConstraintListOfXsFacet [XsFacet]
  deriving (Eq, Ord, Read, Show)

_NodeConstraint = (Core.Name "hydra/langs/shex/syntax.NodeConstraint")

_NodeConstraint_sequence = (Core.Name "sequence")

_NodeConstraint_sequence2 = (Core.Name "sequence2")

_NodeConstraint_sequence3 = (Core.Name "sequence3")

_NodeConstraint_sequence4 = (Core.Name "sequence4")

_NodeConstraint_sequence5 = (Core.Name "sequence5")

_NodeConstraint_listOfXsFacet = (Core.Name "listOfXsFacet")

data NodeConstraint_Sequence2 = 
  NodeConstraint_Sequence2 {
    nodeConstraint_Sequence2NonLiteralKind :: NonLiteralKind,
    nodeConstraint_Sequence2ListOfStringFacet :: [StringFacet]}
  deriving (Eq, Ord, Read, Show)

_NodeConstraint_Sequence2 = (Core.Name "hydra/langs/shex/syntax.NodeConstraint.Sequence2")

_NodeConstraint_Sequence2_nonLiteralKind = (Core.Name "nonLiteralKind")

_NodeConstraint_Sequence2_listOfStringFacet = (Core.Name "listOfStringFacet")

data NodeConstraint_Sequence3 = 
  NodeConstraint_Sequence3 {
    nodeConstraint_Sequence3Datatype :: Datatype,
    nodeConstraint_Sequence3ListOfXsFacet :: [XsFacet]}
  deriving (Eq, Ord, Read, Show)

_NodeConstraint_Sequence3 = (Core.Name "hydra/langs/shex/syntax.NodeConstraint.Sequence3")

_NodeConstraint_Sequence3_datatype = (Core.Name "datatype")

_NodeConstraint_Sequence3_listOfXsFacet = (Core.Name "listOfXsFacet")

data NodeConstraint_Sequence4 = 
  NodeConstraint_Sequence4 {
    nodeConstraint_Sequence4ValueSet :: ValueSet,
    nodeConstraint_Sequence4ListOfXsFacet :: [XsFacet]}
  deriving (Eq, Ord, Read, Show)

_NodeConstraint_Sequence4 = (Core.Name "hydra/langs/shex/syntax.NodeConstraint.Sequence4")

_NodeConstraint_Sequence4_valueSet = (Core.Name "valueSet")

_NodeConstraint_Sequence4_listOfXsFacet = (Core.Name "listOfXsFacet")

data NodeConstraint_Sequence5 = 
  NodeConstraint_Sequence5 {
    nodeConstraint_Sequence5ValueSet :: ValueSet,
    nodeConstraint_Sequence5ListOfXsFacet :: [XsFacet]}
  deriving (Eq, Ord, Read, Show)

_NodeConstraint_Sequence5 = (Core.Name "hydra/langs/shex/syntax.NodeConstraint.Sequence5")

_NodeConstraint_Sequence5_valueSet = (Core.Name "valueSet")

_NodeConstraint_Sequence5_listOfXsFacet = (Core.Name "listOfXsFacet")

data NonLiteralKind = 
  NonLiteralKindIRI  |
  NonLiteralKindBNODE  |
  NonLiteralKindNONLITERAL 
  deriving (Eq, Ord, Read, Show)

_NonLiteralKind = (Core.Name "hydra/langs/shex/syntax.NonLiteralKind")

_NonLiteralKind_iRI = (Core.Name "iRI")

_NonLiteralKind_bNODE = (Core.Name "bNODE")

_NonLiteralKind_nONLITERAL = (Core.Name "nONLITERAL")

data XsFacet = 
  XsFacetStringFacet StringFacet |
  XsFacetNumericFacet NumericFacet
  deriving (Eq, Ord, Read, Show)

_XsFacet = (Core.Name "hydra/langs/shex/syntax.XsFacet")

_XsFacet_stringFacet = (Core.Name "stringFacet")

_XsFacet_numericFacet = (Core.Name "numericFacet")

data StringFacet = 
  StringFacetSequence StringFacet_Sequence |
  StringFacetRegexp Regexp
  deriving (Eq, Ord, Read, Show)

_StringFacet = (Core.Name "hydra/langs/shex/syntax.StringFacet")

_StringFacet_sequence = (Core.Name "sequence")

_StringFacet_regexp = (Core.Name "regexp")

data StringFacet_Sequence = 
  StringFacet_Sequence {
    stringFacet_SequenceStringLength :: StringLength,
    stringFacet_SequenceInteger :: Integer_}
  deriving (Eq, Ord, Read, Show)

_StringFacet_Sequence = (Core.Name "hydra/langs/shex/syntax.StringFacet.Sequence")

_StringFacet_Sequence_stringLength = (Core.Name "stringLength")

_StringFacet_Sequence_integer = (Core.Name "integer")

data StringLength = 
  StringLengthLENGTH  |
  StringLengthMINLENGTH  |
  StringLengthMAXLENGTH 
  deriving (Eq, Ord, Read, Show)

_StringLength = (Core.Name "hydra/langs/shex/syntax.StringLength")

_StringLength_lENGTH = (Core.Name "lENGTH")

_StringLength_mINLENGTH = (Core.Name "mINLENGTH")

_StringLength_mAXLENGTH = (Core.Name "mAXLENGTH")

data NumericFacet = 
  NumericFacetSequence NumericFacet_Sequence |
  NumericFacetSequence2 NumericFacet_Sequence2
  deriving (Eq, Ord, Read, Show)

_NumericFacet = (Core.Name "hydra/langs/shex/syntax.NumericFacet")

_NumericFacet_sequence = (Core.Name "sequence")

_NumericFacet_sequence2 = (Core.Name "sequence2")

data NumericFacet_Sequence = 
  NumericFacet_Sequence {
    numericFacet_SequenceNumericRange :: NumericRange,
    numericFacet_SequenceNumericLiteral :: NumericLiteral}
  deriving (Eq, Ord, Read, Show)

_NumericFacet_Sequence = (Core.Name "hydra/langs/shex/syntax.NumericFacet.Sequence")

_NumericFacet_Sequence_numericRange = (Core.Name "numericRange")

_NumericFacet_Sequence_numericLiteral = (Core.Name "numericLiteral")

data NumericFacet_Sequence2 = 
  NumericFacet_Sequence2 {
    numericFacet_Sequence2NumericLength :: NumericLength,
    numericFacet_Sequence2Integer :: Integer_}
  deriving (Eq, Ord, Read, Show)

_NumericFacet_Sequence2 = (Core.Name "hydra/langs/shex/syntax.NumericFacet.Sequence2")

_NumericFacet_Sequence2_numericLength = (Core.Name "numericLength")

_NumericFacet_Sequence2_integer = (Core.Name "integer")

data NumericRange = 
  NumericRangeMININCLUSIVE  |
  NumericRangeMINEXCLUSIVE  |
  NumericRangeMAXINCLUSIVE  |
  NumericRangeMAXEXCLUSIVE 
  deriving (Eq, Ord, Read, Show)

_NumericRange = (Core.Name "hydra/langs/shex/syntax.NumericRange")

_NumericRange_mININCLUSIVE = (Core.Name "mININCLUSIVE")

_NumericRange_mINEXCLUSIVE = (Core.Name "mINEXCLUSIVE")

_NumericRange_mAXINCLUSIVE = (Core.Name "mAXINCLUSIVE")

_NumericRange_mAXEXCLUSIVE = (Core.Name "mAXEXCLUSIVE")

data NumericLength = 
  NumericLengthTOTALDIGITS  |
  NumericLengthFRACTIONDIGITS 
  deriving (Eq, Ord, Read, Show)

_NumericLength = (Core.Name "hydra/langs/shex/syntax.NumericLength")

_NumericLength_tOTALDIGITS = (Core.Name "tOTALDIGITS")

_NumericLength_fRACTIONDIGITS = (Core.Name "fRACTIONDIGITS")

data ShapeDefinition = 
  ShapeDefinition {
    shapeDefinitionListOfAlts :: [ShapeDefinition_ListOfAlts_Elmt],
    shapeDefinitionTripleExpression :: (Maybe TripleExpression),
    shapeDefinitionListOfAnnotation :: [Annotation],
    shapeDefinitionSemanticActions :: SemanticActions}
  deriving (Eq, Ord, Read, Show)

_ShapeDefinition = (Core.Name "hydra/langs/shex/syntax.ShapeDefinition")

_ShapeDefinition_listOfAlts = (Core.Name "listOfAlts")

_ShapeDefinition_tripleExpression = (Core.Name "tripleExpression")

_ShapeDefinition_listOfAnnotation = (Core.Name "listOfAnnotation")

_ShapeDefinition_semanticActions = (Core.Name "semanticActions")

data ShapeDefinition_ListOfAlts_Elmt = 
  ShapeDefinition_ListOfAlts_ElmtIncludeSet IncludeSet |
  ShapeDefinition_ListOfAlts_ElmtExtraPropertySet ExtraPropertySet |
  ShapeDefinition_ListOfAlts_ElmtCLOSED 
  deriving (Eq, Ord, Read, Show)

_ShapeDefinition_ListOfAlts_Elmt = (Core.Name "hydra/langs/shex/syntax.ShapeDefinition.ListOfAlts.Elmt")

_ShapeDefinition_ListOfAlts_Elmt_includeSet = (Core.Name "includeSet")

_ShapeDefinition_ListOfAlts_Elmt_extraPropertySet = (Core.Name "extraPropertySet")

_ShapeDefinition_ListOfAlts_Elmt_cLOSED = (Core.Name "cLOSED")

data InlineShapeDefinition = 
  InlineShapeDefinition {
    inlineShapeDefinitionListOfAlts :: [InlineShapeDefinition_ListOfAlts_Elmt],
    inlineShapeDefinitionTripleExpression :: (Maybe TripleExpression)}
  deriving (Eq, Ord, Read, Show)

_InlineShapeDefinition = (Core.Name "hydra/langs/shex/syntax.InlineShapeDefinition")

_InlineShapeDefinition_listOfAlts = (Core.Name "listOfAlts")

_InlineShapeDefinition_tripleExpression = (Core.Name "tripleExpression")

data InlineShapeDefinition_ListOfAlts_Elmt = 
  InlineShapeDefinition_ListOfAlts_ElmtIncludeSet IncludeSet |
  InlineShapeDefinition_ListOfAlts_ElmtExtraPropertySet ExtraPropertySet |
  InlineShapeDefinition_ListOfAlts_ElmtCLOSED 
  deriving (Eq, Ord, Read, Show)

_InlineShapeDefinition_ListOfAlts_Elmt = (Core.Name "hydra/langs/shex/syntax.InlineShapeDefinition.ListOfAlts.Elmt")

_InlineShapeDefinition_ListOfAlts_Elmt_includeSet = (Core.Name "includeSet")

_InlineShapeDefinition_ListOfAlts_Elmt_extraPropertySet = (Core.Name "extraPropertySet")

_InlineShapeDefinition_ListOfAlts_Elmt_cLOSED = (Core.Name "cLOSED")

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

_OneOfTripleExpr_groupTripleExpr = (Core.Name "groupTripleExpr")

_OneOfTripleExpr_multiElementOneOf = (Core.Name "multiElementOneOf")

data MultiElementOneOf = 
  MultiElementOneOf {
    multiElementOneOfGroupTripleExpr :: GroupTripleExpr,
    multiElementOneOfListOfSequence :: [GroupTripleExpr]}
  deriving (Eq, Ord, Read, Show)

_MultiElementOneOf = (Core.Name "hydra/langs/shex/syntax.MultiElementOneOf")

_MultiElementOneOf_groupTripleExpr = (Core.Name "groupTripleExpr")

_MultiElementOneOf_listOfSequence = (Core.Name "listOfSequence")

data InnerTripleExpr = 
  InnerTripleExprMultiElementGroup MultiElementGroup |
  InnerTripleExprMultiElementOneOf MultiElementOneOf
  deriving (Eq, Ord, Read, Show)

_InnerTripleExpr = (Core.Name "hydra/langs/shex/syntax.InnerTripleExpr")

_InnerTripleExpr_multiElementGroup = (Core.Name "multiElementGroup")

_InnerTripleExpr_multiElementOneOf = (Core.Name "multiElementOneOf")

data GroupTripleExpr = 
  GroupTripleExprSingleElementGroup SingleElementGroup |
  GroupTripleExprMultiElementGroup MultiElementGroup
  deriving (Eq, Ord, Read, Show)

_GroupTripleExpr = (Core.Name "hydra/langs/shex/syntax.GroupTripleExpr")

_GroupTripleExpr_singleElementGroup = (Core.Name "singleElementGroup")

_GroupTripleExpr_multiElementGroup = (Core.Name "multiElementGroup")

data SingleElementGroup = 
  SingleElementGroup {
    singleElementGroupUnaryTripleExpr :: UnaryTripleExpr,
    singleElementGroupSemi :: (Maybe ())}
  deriving (Eq, Ord, Read, Show)

_SingleElementGroup = (Core.Name "hydra/langs/shex/syntax.SingleElementGroup")

_SingleElementGroup_unaryTripleExpr = (Core.Name "unaryTripleExpr")

_SingleElementGroup_semi = (Core.Name "semi")

data MultiElementGroup = 
  MultiElementGroup {
    multiElementGroupUnaryTripleExpr :: UnaryTripleExpr,
    multiElementGroupListOfSequence :: [UnaryTripleExpr],
    multiElementGroupSemi :: (Maybe ())}
  deriving (Eq, Ord, Read, Show)

_MultiElementGroup = (Core.Name "hydra/langs/shex/syntax.MultiElementGroup")

_MultiElementGroup_unaryTripleExpr = (Core.Name "unaryTripleExpr")

_MultiElementGroup_listOfSequence = (Core.Name "listOfSequence")

_MultiElementGroup_semi = (Core.Name "semi")

data UnaryTripleExpr = 
  UnaryTripleExprSequence UnaryTripleExpr_Sequence |
  UnaryTripleExprInclude Include
  deriving (Eq, Ord, Read, Show)

_UnaryTripleExpr = (Core.Name "hydra/langs/shex/syntax.UnaryTripleExpr")

_UnaryTripleExpr_sequence = (Core.Name "sequence")

_UnaryTripleExpr_include = (Core.Name "include")

data UnaryTripleExpr_Sequence = 
  UnaryTripleExpr_Sequence {
    unaryTripleExpr_SequenceSequence :: (Maybe TripleExprLabel),
    unaryTripleExpr_SequenceAlts :: UnaryTripleExpr_Sequence_Alts}
  deriving (Eq, Ord, Read, Show)

_UnaryTripleExpr_Sequence = (Core.Name "hydra/langs/shex/syntax.UnaryTripleExpr.Sequence")

_UnaryTripleExpr_Sequence_sequence = (Core.Name "sequence")

_UnaryTripleExpr_Sequence_alts = (Core.Name "alts")

data UnaryTripleExpr_Sequence_Alts = 
  UnaryTripleExpr_Sequence_AltsTripleConstraint TripleConstraint |
  UnaryTripleExpr_Sequence_AltsBracketedTripleExpr BracketedTripleExpr
  deriving (Eq, Ord, Read, Show)

_UnaryTripleExpr_Sequence_Alts = (Core.Name "hydra/langs/shex/syntax.UnaryTripleExpr.Sequence.Alts")

_UnaryTripleExpr_Sequence_Alts_tripleConstraint = (Core.Name "tripleConstraint")

_UnaryTripleExpr_Sequence_Alts_bracketedTripleExpr = (Core.Name "bracketedTripleExpr")

data BracketedTripleExpr = 
  BracketedTripleExpr {
    bracketedTripleExprInnerTripleExpr :: InnerTripleExpr,
    bracketedTripleExprCardinality :: (Maybe Cardinality),
    bracketedTripleExprListOfAnnotation :: [Annotation],
    bracketedTripleExprSemanticActions :: SemanticActions}
  deriving (Eq, Ord, Read, Show)

_BracketedTripleExpr = (Core.Name "hydra/langs/shex/syntax.BracketedTripleExpr")

_BracketedTripleExpr_innerTripleExpr = (Core.Name "innerTripleExpr")

_BracketedTripleExpr_cardinality = (Core.Name "cardinality")

_BracketedTripleExpr_listOfAnnotation = (Core.Name "listOfAnnotation")

_BracketedTripleExpr_semanticActions = (Core.Name "semanticActions")

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

_TripleConstraint_senseFlags = (Core.Name "senseFlags")

_TripleConstraint_predicate = (Core.Name "predicate")

_TripleConstraint_inlineShapeExpression = (Core.Name "inlineShapeExpression")

_TripleConstraint_cardinality = (Core.Name "cardinality")

_TripleConstraint_listOfAnnotation = (Core.Name "listOfAnnotation")

_TripleConstraint_semanticActions = (Core.Name "semanticActions")

data Cardinality = 
  CardinalityAst  |
  CardinalityPlus  |
  CardinalityQuest  |
  CardinalityRepeatRange RepeatRange
  deriving (Eq, Ord, Read, Show)

_Cardinality = (Core.Name "hydra/langs/shex/syntax.Cardinality")

_Cardinality_ast = (Core.Name "ast")

_Cardinality_plus = (Core.Name "plus")

_Cardinality_quest = (Core.Name "quest")

_Cardinality_repeatRange = (Core.Name "repeatRange")

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

_ValueSetValue_iriRange = (Core.Name "iriRange")

_ValueSetValue_literal = (Core.Name "literal")

data IriRange = 
  IriRangeSequence IriRange_Sequence |
  IriRangeSequence2 [Exclusion]
  deriving (Eq, Ord, Read, Show)

_IriRange = (Core.Name "hydra/langs/shex/syntax.IriRange")

_IriRange_sequence = (Core.Name "sequence")

_IriRange_sequence2 = (Core.Name "sequence2")

data IriRange_Sequence = 
  IriRange_Sequence {
    iriRange_SequenceIri :: Iri,
    iriRange_SequenceSequence :: (Maybe [Exclusion])}
  deriving (Eq, Ord, Read, Show)

_IriRange_Sequence = (Core.Name "hydra/langs/shex/syntax.IriRange.Sequence")

_IriRange_Sequence_iri = (Core.Name "iri")

_IriRange_Sequence_sequence = (Core.Name "sequence")

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

_Annotation_predicate = (Core.Name "predicate")

_Annotation_alts = (Core.Name "alts")

data Annotation_Alts = 
  Annotation_AltsIri Iri |
  Annotation_AltsLiteral Literal
  deriving (Eq, Ord, Read, Show)

_Annotation_Alts = (Core.Name "hydra/langs/shex/syntax.Annotation.Alts")

_Annotation_Alts_iri = (Core.Name "iri")

_Annotation_Alts_literal = (Core.Name "literal")

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

_CodeDecl_iri = (Core.Name "iri")

_CodeDecl_alts = (Core.Name "alts")

data CodeDecl_Alts = 
  CodeDecl_AltsCode Code |
  CodeDecl_AltsPercnt 
  deriving (Eq, Ord, Read, Show)

_CodeDecl_Alts = (Core.Name "hydra/langs/shex/syntax.CodeDecl.Alts")

_CodeDecl_Alts_code = (Core.Name "code")

_CodeDecl_Alts_percnt = (Core.Name "percnt")

data Literal = 
  LiteralRdfLiteral RdfLiteral |
  LiteralNumericLiteral NumericLiteral |
  LiteralBooleanLiteral BooleanLiteral
  deriving (Eq, Ord, Read, Show)

_Literal = (Core.Name "hydra/langs/shex/syntax.Literal")

_Literal_rdfLiteral = (Core.Name "rdfLiteral")

_Literal_numericLiteral = (Core.Name "numericLiteral")

_Literal_booleanLiteral = (Core.Name "booleanLiteral")

data Predicate = 
  PredicateIri Iri |
  PredicateRdfType RdfType
  deriving (Eq, Ord, Read, Show)

_Predicate = (Core.Name "hydra/langs/shex/syntax.Predicate")

_Predicate_iri = (Core.Name "iri")

_Predicate_rdfType = (Core.Name "rdfType")

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

_ShapeExprLabel_iri = (Core.Name "iri")

_ShapeExprLabel_blankNode = (Core.Name "blankNode")

data TripleExprLabel = 
  TripleExprLabelIri Iri |
  TripleExprLabelBlankNode BlankNode
  deriving (Eq, Ord, Read, Show)

_TripleExprLabel = (Core.Name "hydra/langs/shex/syntax.TripleExprLabel")

_TripleExprLabel_iri = (Core.Name "iri")

_TripleExprLabel_blankNode = (Core.Name "blankNode")

data NumericLiteral = 
  NumericLiteralInteger Integer_ |
  NumericLiteralDecimal Decimal |
  NumericLiteralDouble Double_
  deriving (Eq, Ord, Read, Show)

_NumericLiteral = (Core.Name "hydra/langs/shex/syntax.NumericLiteral")

_NumericLiteral_integer = (Core.Name "integer")

_NumericLiteral_decimal = (Core.Name "decimal")

_NumericLiteral_double = (Core.Name "double")

data RdfLiteral = 
  RdfLiteral {
    rdfLiteralString :: String_,
    rdfLiteralAlts :: (Maybe RdfLiteral_Alts_Option)}
  deriving (Eq, Ord, Read, Show)

_RdfLiteral = (Core.Name "hydra/langs/shex/syntax.RdfLiteral")

_RdfLiteral_string = (Core.Name "string")

_RdfLiteral_alts = (Core.Name "alts")

data RdfLiteral_Alts_Option = 
  RdfLiteral_Alts_OptionLangTag LangTag |
  RdfLiteral_Alts_OptionSequence Datatype
  deriving (Eq, Ord, Read, Show)

_RdfLiteral_Alts_Option = (Core.Name "hydra/langs/shex/syntax.RdfLiteral.Alts.Option")

_RdfLiteral_Alts_Option_langTag = (Core.Name "langTag")

_RdfLiteral_Alts_Option_sequence = (Core.Name "sequence")

data BooleanLiteral = 
  BooleanLiteralTrue  |
  BooleanLiteralFalse 
  deriving (Eq, Ord, Read, Show)

_BooleanLiteral = (Core.Name "hydra/langs/shex/syntax.BooleanLiteral")

_BooleanLiteral_true = (Core.Name "true")

_BooleanLiteral_false = (Core.Name "false")

data String_ = 
  StringStringLiteral1 StringLiteral1 |
  StringStringLiteralLong1 StringLiteralLong1 |
  StringStringLiteral2 StringLiteral2 |
  StringStringLiteralLong2 StringLiteralLong2
  deriving (Eq, Ord, Read, Show)

_String = (Core.Name "hydra/langs/shex/syntax.String")

_String_stringLiteral1 = (Core.Name "stringLiteral1")

_String_stringLiteralLong1 = (Core.Name "stringLiteralLong1")

_String_stringLiteral2 = (Core.Name "stringLiteral2")

_String_stringLiteralLong2 = (Core.Name "stringLiteralLong2")

data Iri = 
  IriIriRef IriRef |
  IriPrefixedName PrefixedName
  deriving (Eq, Ord, Read, Show)

_Iri = (Core.Name "hydra/langs/shex/syntax.Iri")

_Iri_iriRef = (Core.Name "iriRef")

_Iri_prefixedName = (Core.Name "prefixedName")

data PrefixedName = 
  PrefixedNamePnameLn PnameLn |
  PrefixedNamePnameNs PnameNs
  deriving (Eq, Ord, Read, Show)

_PrefixedName = (Core.Name "hydra/langs/shex/syntax.PrefixedName")

_PrefixedName_pnameLn = (Core.Name "pnameLn")

_PrefixedName_pnameNs = (Core.Name "pnameNs")

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

_Code_Elmt_regex = (Core.Name "regex")

_Code_Elmt_sequence = (Core.Name "sequence")

_Code_Elmt_uchar = (Core.Name "uchar")

data RepeatRange = 
  RepeatRange {
    repeatRangeInteger :: Integer_,
    repeatRangeSequence :: (Maybe (Maybe (Maybe RepeatRange_Sequence_Option_Option_Option)))}
  deriving (Eq, Ord, Read, Show)

_RepeatRange = (Core.Name "hydra/langs/shex/syntax.RepeatRange")

_RepeatRange_integer = (Core.Name "integer")

_RepeatRange_sequence = (Core.Name "sequence")

data RepeatRange_Sequence_Option_Option_Option = 
  RepeatRange_Sequence_Option_Option_OptionInteger Integer_ |
  RepeatRange_Sequence_Option_Option_OptionAst 
  deriving (Eq, Ord, Read, Show)

_RepeatRange_Sequence_Option_Option_Option = (Core.Name "hydra/langs/shex/syntax.RepeatRange.Sequence.Option.Option.Option")

_RepeatRange_Sequence_Option_Option_Option_integer = (Core.Name "integer")

_RepeatRange_Sequence_Option_Option_Option_ast = (Core.Name "ast")

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

_IriRef_Elmt_regex = (Core.Name "regex")

_IriRef_Elmt_uchar = (Core.Name "uchar")

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

_PnameLn_pnameNs = (Core.Name "pnameNs")

_PnameLn_pnLocal = (Core.Name "pnLocal")

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

_AtpNameLn_pnameNs = (Core.Name "pnameNs")

_AtpNameLn_pnLocal = (Core.Name "pnLocal")

data Regexp = 
  Regexp {
    regexpListOfAlts :: [Regexp_ListOfAlts_Elmt],
    regexpListOfRegex :: [String]}
  deriving (Eq, Ord, Read, Show)

_Regexp = (Core.Name "hydra/langs/shex/syntax.Regexp")

_Regexp_listOfAlts = (Core.Name "listOfAlts")

_Regexp_listOfRegex = (Core.Name "listOfRegex")

data Regexp_ListOfAlts_Elmt = 
  Regexp_ListOfAlts_ElmtRegex String |
  Regexp_ListOfAlts_ElmtSequence String |
  Regexp_ListOfAlts_ElmtUchar Uchar
  deriving (Eq, Ord, Read, Show)

_Regexp_ListOfAlts_Elmt = (Core.Name "hydra/langs/shex/syntax.Regexp.ListOfAlts.Elmt")

_Regexp_ListOfAlts_Elmt_regex = (Core.Name "regex")

_Regexp_ListOfAlts_Elmt_sequence = (Core.Name "sequence")

_Regexp_ListOfAlts_Elmt_uchar = (Core.Name "uchar")

data BlankNodeLabel = 
  BlankNodeLabel {
    blankNodeLabelAlts :: BlankNodeLabel_Alts,
    blankNodeLabelListOfAlts :: (Maybe [BlankNodeLabel_ListOfAlts_Option_Elmt]),
    blankNodeLabelPnChars :: PnChars}
  deriving (Eq, Ord, Read, Show)

_BlankNodeLabel = (Core.Name "hydra/langs/shex/syntax.BlankNodeLabel")

_BlankNodeLabel_alts = (Core.Name "alts")

_BlankNodeLabel_listOfAlts = (Core.Name "listOfAlts")

_BlankNodeLabel_pnChars = (Core.Name "pnChars")

data BlankNodeLabel_Alts = 
  BlankNodeLabel_AltsPnCharsU PnCharsU |
  BlankNodeLabel_AltsRegex String
  deriving (Eq, Ord, Read, Show)

_BlankNodeLabel_Alts = (Core.Name "hydra/langs/shex/syntax.BlankNodeLabel.Alts")

_BlankNodeLabel_Alts_pnCharsU = (Core.Name "pnCharsU")

_BlankNodeLabel_Alts_regex = (Core.Name "regex")

data BlankNodeLabel_ListOfAlts_Option_Elmt = 
  BlankNodeLabel_ListOfAlts_Option_ElmtPnChars PnChars |
  BlankNodeLabel_ListOfAlts_Option_ElmtPeriod 
  deriving (Eq, Ord, Read, Show)

_BlankNodeLabel_ListOfAlts_Option_Elmt = (Core.Name "hydra/langs/shex/syntax.BlankNodeLabel.ListOfAlts.Option.Elmt")

_BlankNodeLabel_ListOfAlts_Option_Elmt_pnChars = (Core.Name "pnChars")

_BlankNodeLabel_ListOfAlts_Option_Elmt_period = (Core.Name "period")

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

_StringLiteral1_Elmt_regex = (Core.Name "regex")

_StringLiteral1_Elmt_echar = (Core.Name "echar")

_StringLiteral1_Elmt_uchar = (Core.Name "uchar")

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

_StringLiteral2_Elmt_regex = (Core.Name "regex")

_StringLiteral2_Elmt_echar = (Core.Name "echar")

_StringLiteral2_Elmt_uchar = (Core.Name "uchar")

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

_StringLiteralLong1_Elmt_sequence = (Core.Name "sequence")

_StringLiteralLong1_Elmt_echar = (Core.Name "echar")

_StringLiteralLong1_Elmt_uchar = (Core.Name "uchar")

data StringLiteralLong1_Elmt_Sequence = 
  StringLiteralLong1_Elmt_Sequence {
    stringLiteralLong1_Elmt_SequenceAlts :: (Maybe StringLiteralLong1_Elmt_Sequence_Alts_Option),
    stringLiteralLong1_Elmt_SequenceRegex :: String}
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong1_Elmt_Sequence = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong1.Elmt.Sequence")

_StringLiteralLong1_Elmt_Sequence_alts = (Core.Name "alts")

_StringLiteralLong1_Elmt_Sequence_regex = (Core.Name "regex")

data StringLiteralLong1_Elmt_Sequence_Alts_Option = 
  StringLiteralLong1_Elmt_Sequence_Alts_OptionApos  |
  StringLiteralLong1_Elmt_Sequence_Alts_OptionSequence StringLiteralLong1_Elmt_Sequence_Alts_Option_Sequence
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong1_Elmt_Sequence_Alts_Option = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong1.Elmt.Sequence.Alts.Option")

_StringLiteralLong1_Elmt_Sequence_Alts_Option_apos = (Core.Name "apos")

_StringLiteralLong1_Elmt_Sequence_Alts_Option_sequence = (Core.Name "sequence")

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

_StringLiteralLong2_Elmt_sequence = (Core.Name "sequence")

_StringLiteralLong2_Elmt_echar = (Core.Name "echar")

_StringLiteralLong2_Elmt_uchar = (Core.Name "uchar")

data StringLiteralLong2_Elmt_Sequence = 
  StringLiteralLong2_Elmt_Sequence {
    stringLiteralLong2_Elmt_SequenceAlts :: (Maybe StringLiteralLong2_Elmt_Sequence_Alts_Option),
    stringLiteralLong2_Elmt_SequenceRegex :: String}
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong2_Elmt_Sequence = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong2.Elmt.Sequence")

_StringLiteralLong2_Elmt_Sequence_alts = (Core.Name "alts")

_StringLiteralLong2_Elmt_Sequence_regex = (Core.Name "regex")

data StringLiteralLong2_Elmt_Sequence_Alts_Option = 
  StringLiteralLong2_Elmt_Sequence_Alts_OptionQuot  |
  StringLiteralLong2_Elmt_Sequence_Alts_OptionSequence StringLiteralLong2_Elmt_Sequence_Alts_Option_Sequence
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong2_Elmt_Sequence_Alts_Option = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong2.Elmt.Sequence.Alts.Option")

_StringLiteralLong2_Elmt_Sequence_Alts_Option_quot = (Core.Name "quot")

_StringLiteralLong2_Elmt_Sequence_Alts_Option_sequence = (Core.Name "sequence")

data StringLiteralLong2_Elmt_Sequence_Alts_Option_Sequence = 
  StringLiteralLong2_Elmt_Sequence_Alts_Option_Sequence {}
  deriving (Eq, Ord, Read, Show)

_StringLiteralLong2_Elmt_Sequence_Alts_Option_Sequence = (Core.Name "hydra/langs/shex/syntax.StringLiteralLong2.Elmt.Sequence.Alts.Option.Sequence")

data Uchar = 
  UcharSequence Uchar_Sequence |
  UcharSequence2 Uchar_Sequence2
  deriving (Eq, Ord, Read, Show)

_Uchar = (Core.Name "hydra/langs/shex/syntax.Uchar")

_Uchar_sequence = (Core.Name "sequence")

_Uchar_sequence2 = (Core.Name "sequence2")

data Uchar_Sequence = 
  Uchar_Sequence {
    uchar_SequenceHex :: Hex,
    uchar_SequenceHex2 :: Hex,
    uchar_SequenceHex3 :: Hex,
    uchar_SequenceHex4 :: Hex}
  deriving (Eq, Ord, Read, Show)

_Uchar_Sequence = (Core.Name "hydra/langs/shex/syntax.Uchar.Sequence")

_Uchar_Sequence_hex = (Core.Name "hex")

_Uchar_Sequence_hex2 = (Core.Name "hex2")

_Uchar_Sequence_hex3 = (Core.Name "hex3")

_Uchar_Sequence_hex4 = (Core.Name "hex4")

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

_Uchar_Sequence2_hex = (Core.Name "hex")

_Uchar_Sequence2_hex2 = (Core.Name "hex2")

_Uchar_Sequence2_hex3 = (Core.Name "hex3")

_Uchar_Sequence2_hex4 = (Core.Name "hex4")

_Uchar_Sequence2_hex5 = (Core.Name "hex5")

_Uchar_Sequence2_hex6 = (Core.Name "hex6")

_Uchar_Sequence2_hex7 = (Core.Name "hex7")

_Uchar_Sequence2_hex8 = (Core.Name "hex8")

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

_PnCharsBase_regex = (Core.Name "regex")

_PnCharsBase_regex2 = (Core.Name "regex2")

data PnCharsU = 
  PnCharsUPnCharsBase PnCharsBase |
  PnCharsULowbar 
  deriving (Eq, Ord, Read, Show)

_PnCharsU = (Core.Name "hydra/langs/shex/syntax.PnCharsU")

_PnCharsU_pnCharsBase = (Core.Name "pnCharsBase")

_PnCharsU_lowbar = (Core.Name "lowbar")

data PnChars = 
  PnCharsPnCharsU PnCharsU |
  PnCharsMinus  |
  PnCharsRegex String
  deriving (Eq, Ord, Read, Show)

_PnChars = (Core.Name "hydra/langs/shex/syntax.PnChars")

_PnChars_pnCharsU = (Core.Name "pnCharsU")

_PnChars_minus = (Core.Name "minus")

_PnChars_regex = (Core.Name "regex")

data PnPrefix = 
  PnPrefix {
    pnPrefixPnCharsBase :: PnCharsBase,
    pnPrefixSequence :: (Maybe PnPrefix_Sequence_Option)}
  deriving (Eq, Ord, Read, Show)

_PnPrefix = (Core.Name "hydra/langs/shex/syntax.PnPrefix")

_PnPrefix_pnCharsBase = (Core.Name "pnCharsBase")

_PnPrefix_sequence = (Core.Name "sequence")

data PnPrefix_Sequence_Option = 
  PnPrefix_Sequence_Option {
    pnPrefix_Sequence_OptionAlts :: PnPrefix_Sequence_Option_Alts,
    pnPrefix_Sequence_OptionPnChars :: PnChars}
  deriving (Eq, Ord, Read, Show)

_PnPrefix_Sequence_Option = (Core.Name "hydra/langs/shex/syntax.PnPrefix.Sequence.Option")

_PnPrefix_Sequence_Option_alts = (Core.Name "alts")

_PnPrefix_Sequence_Option_pnChars = (Core.Name "pnChars")

data PnPrefix_Sequence_Option_Alts = 
  PnPrefix_Sequence_Option_AltsPnChars PnChars |
  PnPrefix_Sequence_Option_AltsPeriod 
  deriving (Eq, Ord, Read, Show)

_PnPrefix_Sequence_Option_Alts = (Core.Name "hydra/langs/shex/syntax.PnPrefix.Sequence.Option.Alts")

_PnPrefix_Sequence_Option_Alts_pnChars = (Core.Name "pnChars")

_PnPrefix_Sequence_Option_Alts_period = (Core.Name "period")

data PnLocal = 
  PnLocal {
    pnLocalAlts :: PnLocal_Alts,
    pnLocalSequence :: (Maybe PnLocal_Sequence_Option)}
  deriving (Eq, Ord, Read, Show)

_PnLocal = (Core.Name "hydra/langs/shex/syntax.PnLocal")

_PnLocal_alts = (Core.Name "alts")

_PnLocal_sequence = (Core.Name "sequence")

data PnLocal_Alts = 
  PnLocal_AltsPnCharsU PnCharsU |
  PnLocal_AltsColon  |
  PnLocal_AltsRegex String |
  PnLocal_AltsPlx Plx
  deriving (Eq, Ord, Read, Show)

_PnLocal_Alts = (Core.Name "hydra/langs/shex/syntax.PnLocal.Alts")

_PnLocal_Alts_pnCharsU = (Core.Name "pnCharsU")

_PnLocal_Alts_colon = (Core.Name "colon")

_PnLocal_Alts_regex = (Core.Name "regex")

_PnLocal_Alts_plx = (Core.Name "plx")

data PnLocal_Sequence_Option = 
  PnLocal_Sequence_Option {
    pnLocal_Sequence_OptionListOfAlts :: [PnLocal_Sequence_Option_ListOfAlts_Elmt],
    pnLocal_Sequence_OptionAlts :: PnLocal_Sequence_Option_Alts}
  deriving (Eq, Ord, Read, Show)

_PnLocal_Sequence_Option = (Core.Name "hydra/langs/shex/syntax.PnLocal.Sequence.Option")

_PnLocal_Sequence_Option_listOfAlts = (Core.Name "listOfAlts")

_PnLocal_Sequence_Option_alts = (Core.Name "alts")

data PnLocal_Sequence_Option_ListOfAlts_Elmt = 
  PnLocal_Sequence_Option_ListOfAlts_ElmtPnChars PnChars |
  PnLocal_Sequence_Option_ListOfAlts_ElmtPeriod  |
  PnLocal_Sequence_Option_ListOfAlts_ElmtColon  |
  PnLocal_Sequence_Option_ListOfAlts_ElmtPlx Plx
  deriving (Eq, Ord, Read, Show)

_PnLocal_Sequence_Option_ListOfAlts_Elmt = (Core.Name "hydra/langs/shex/syntax.PnLocal.Sequence.Option.ListOfAlts.Elmt")

_PnLocal_Sequence_Option_ListOfAlts_Elmt_pnChars = (Core.Name "pnChars")

_PnLocal_Sequence_Option_ListOfAlts_Elmt_period = (Core.Name "period")

_PnLocal_Sequence_Option_ListOfAlts_Elmt_colon = (Core.Name "colon")

_PnLocal_Sequence_Option_ListOfAlts_Elmt_plx = (Core.Name "plx")

data PnLocal_Sequence_Option_Alts = 
  PnLocal_Sequence_Option_AltsPnChars PnChars |
  PnLocal_Sequence_Option_AltsColon  |
  PnLocal_Sequence_Option_AltsPlx Plx
  deriving (Eq, Ord, Read, Show)

_PnLocal_Sequence_Option_Alts = (Core.Name "hydra/langs/shex/syntax.PnLocal.Sequence.Option.Alts")

_PnLocal_Sequence_Option_Alts_pnChars = (Core.Name "pnChars")

_PnLocal_Sequence_Option_Alts_colon = (Core.Name "colon")

_PnLocal_Sequence_Option_Alts_plx = (Core.Name "plx")

data Plx = 
  PlxPercent Percent |
  PlxPnLocalEsc PnLocalEsc
  deriving (Eq, Ord, Read, Show)

_Plx = (Core.Name "hydra/langs/shex/syntax.Plx")

_Plx_percent = (Core.Name "percent")

_Plx_pnLocalEsc = (Core.Name "pnLocalEsc")

data Percent = 
  Percent {
    percentHex :: Hex,
    percentHex2 :: Hex}
  deriving (Eq, Ord, Read, Show)

_Percent = (Core.Name "hydra/langs/shex/syntax.Percent")

_Percent_hex = (Core.Name "hex")

_Percent_hex2 = (Core.Name "hex2")

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
