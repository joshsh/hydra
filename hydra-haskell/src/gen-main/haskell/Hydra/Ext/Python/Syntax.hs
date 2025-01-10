-- | A Python syntax model, based on the Python v3 PEG grammar retrieved on 2024-12-22 from https://docs.python.org/3/reference/grammar.html

module Hydra.Ext.Python.Syntax where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

data Module = 
  Module {
    moduleImports :: [ImportStatement],
    moduleBody :: [StatementWithComment],
    moduleComment :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_Module = (Core.Name "hydra/ext/python/syntax.Module")

_Module_imports = (Core.Name "imports")

_Module_body = (Core.Name "body")

_Module_comment = (Core.Name "comment")

data StatementWithComment = 
  StatementWithComment {
    statementWithCommentStatement :: Statement,
    statementWithCommentComment :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_StatementWithComment = (Core.Name "hydra/ext/python/syntax.StatementWithComment")

_StatementWithComment_statement = (Core.Name "statement")

_StatementWithComment_comment = (Core.Name "comment")

newtype Name = 
  Name {
    unName :: String}
  deriving (Eq, Ord, Read, Show)

_Name = (Core.Name "hydra/ext/python/syntax.Name")

data Number = 
  NumberInteger Integer |
  NumberFloat Double
  deriving (Eq, Ord, Read, Show)

_Number = (Core.Name "hydra/ext/python/syntax.Number")

_Number_integer = (Core.Name "integer")

_Number_float = (Core.Name "float")

newtype TypeComment = 
  TypeComment {
    unTypeComment :: String}
  deriving (Eq, Ord, Read, Show)

_TypeComment = (Core.Name "hydra/ext/python/syntax.TypeComment")

newtype File = 
  File {
    unFile :: [Statement]}
  deriving (Eq, Ord, Read, Show)

_File = (Core.Name "hydra/ext/python/syntax.File")

newtype Interactive = 
  Interactive {
    unInteractive :: Statement}
  deriving (Eq, Ord, Read, Show)

_Interactive = (Core.Name "hydra/ext/python/syntax.Interactive")

newtype Eval = 
  Eval {
    unEval :: [Expression]}
  deriving (Eq, Ord, Read, Show)

_Eval = (Core.Name "hydra/ext/python/syntax.Eval")

data FuncType = 
  FuncType {
    funcTypeType :: [TypeExpression],
    funcTypeBody :: Expression}
  deriving (Eq, Ord, Read, Show)

_FuncType = (Core.Name "hydra/ext/python/syntax.FuncType")

_FuncType_type = (Core.Name "type")

_FuncType_body = (Core.Name "body")

data Statement = 
  StatementCompound CompoundStatement |
  StatementSimple [SimpleStatement]
  deriving (Eq, Ord, Read, Show)

_Statement = (Core.Name "hydra/ext/python/syntax.Statement")

_Statement_compound = (Core.Name "compound")

_Statement_simple = (Core.Name "simple")

data SimpleStatement = 
  SimpleStatementAssignment Assignment |
  SimpleStatementTypeAlias TypeAlias |
  SimpleStatementStarExpressions [StarExpression] |
  SimpleStatementReturn ReturnStatement |
  SimpleStatementImport ImportStatement |
  SimpleStatementRaise RaiseStatement |
  SimpleStatementPass  |
  SimpleStatementDel DelStatement |
  SimpleStatementYield YieldStatement |
  SimpleStatementAssert AssertStatement |
  SimpleStatementBreak  |
  SimpleStatementContinue  |
  SimpleStatementGlobal [Name] |
  SimpleStatementNonlocal [Name]
  deriving (Eq, Ord, Read, Show)

_SimpleStatement = (Core.Name "hydra/ext/python/syntax.SimpleStatement")

_SimpleStatement_assignment = (Core.Name "assignment")

_SimpleStatement_typeAlias = (Core.Name "typeAlias")

_SimpleStatement_starExpressions = (Core.Name "starExpressions")

_SimpleStatement_return = (Core.Name "return")

_SimpleStatement_import = (Core.Name "import")

_SimpleStatement_raise = (Core.Name "raise")

_SimpleStatement_pass = (Core.Name "pass")

_SimpleStatement_del = (Core.Name "del")

_SimpleStatement_yield = (Core.Name "yield")

_SimpleStatement_assert = (Core.Name "assert")

_SimpleStatement_break = (Core.Name "break")

_SimpleStatement_continue = (Core.Name "continue")

_SimpleStatement_global = (Core.Name "global")

_SimpleStatement_nonlocal = (Core.Name "nonlocal")

data CompoundStatement = 
  CompoundStatementFunctionDef FunctionDefinition |
  CompoundStatementIf IfStatement |
  CompoundStatementClassDef ClassDefinition |
  CompoundStatementWith WithStatement |
  CompoundStatementFor ForStatement |
  CompoundStatementTry TryStatement |
  CompoundStatementWhile WhileStatement |
  CompoundStatementMatch MatchStatement
  deriving (Eq, Ord, Read, Show)

_CompoundStatement = (Core.Name "hydra/ext/python/syntax.CompoundStatement")

_CompoundStatement_functionDef = (Core.Name "functionDef")

_CompoundStatement_if = (Core.Name "if")

_CompoundStatement_classDef = (Core.Name "classDef")

_CompoundStatement_with = (Core.Name "with")

_CompoundStatement_for = (Core.Name "for")

_CompoundStatement_try = (Core.Name "try")

_CompoundStatement_while = (Core.Name "while")

_CompoundStatement_match = (Core.Name "match")

data Assignment = 
  AssignmentTyped TypedAssignment |
  AssignmentUntyped UntypedAssignment |
  AssignmentAug AugAssignment
  deriving (Eq, Ord, Read, Show)

_Assignment = (Core.Name "hydra/ext/python/syntax.Assignment")

_Assignment_typed = (Core.Name "typed")

_Assignment_untyped = (Core.Name "untyped")

_Assignment_aug = (Core.Name "aug")

data TypedAssignment = 
  TypedAssignment {
    typedAssignmentLhs :: SingleTarget,
    typedAssignmentType :: Expression,
    typedAssignmentRhs :: (Maybe AnnotatedRhs)}
  deriving (Eq, Ord, Read, Show)

_TypedAssignment = (Core.Name "hydra/ext/python/syntax.TypedAssignment")

_TypedAssignment_lhs = (Core.Name "lhs")

_TypedAssignment_type = (Core.Name "type")

_TypedAssignment_rhs = (Core.Name "rhs")

data UntypedAssignment = 
  UntypedAssignment {
    untypedAssignmentTargets :: [StarTarget],
    untypedAssignmentRhs :: AnnotatedRhs,
    untypedAssignmentTypeComment :: (Maybe TypeComment)}
  deriving (Eq, Ord, Read, Show)

_UntypedAssignment = (Core.Name "hydra/ext/python/syntax.UntypedAssignment")

_UntypedAssignment_targets = (Core.Name "targets")

_UntypedAssignment_rhs = (Core.Name "rhs")

_UntypedAssignment_typeComment = (Core.Name "typeComment")

data AugAssignment = 
  AugAssignment {
    augAssignmentLhs :: SingleTarget,
    augAssignmentAugassign :: AugAssign,
    augAssignmentRhs :: AnnotatedRhs}
  deriving (Eq, Ord, Read, Show)

_AugAssignment = (Core.Name "hydra/ext/python/syntax.AugAssignment")

_AugAssignment_lhs = (Core.Name "lhs")

_AugAssignment_augassign = (Core.Name "augassign")

_AugAssignment_rhs = (Core.Name "rhs")

data AnnotatedRhs = 
  AnnotatedRhsYield YieldExpression |
  AnnotatedRhsStar [StarExpression]
  deriving (Eq, Ord, Read, Show)

_AnnotatedRhs = (Core.Name "hydra/ext/python/syntax.AnnotatedRhs")

_AnnotatedRhs_yield = (Core.Name "yield")

_AnnotatedRhs_star = (Core.Name "star")

data AugAssign = 
  AugAssignPlusEqual  |
  AugAssignMinusEqual  |
  AugAssignTimesEqual  |
  AugAssignAtEqual  |
  AugAssignSlashEqual  |
  AugAssignPercentEqual  |
  AugAssignAmpersandEqual  |
  AugAssignBarEqual  |
  AugAssignCaretEqual  |
  AugAssignLeftShiftEqual  |
  AugAssignRightShiftEqual  |
  AugAssignStarStarEqual  |
  AugAssignDoubleSlashEqual 
  deriving (Eq, Ord, Read, Show)

_AugAssign = (Core.Name "hydra/ext/python/syntax.AugAssign")

_AugAssign_plusEqual = (Core.Name "plusEqual")

_AugAssign_minusEqual = (Core.Name "minusEqual")

_AugAssign_timesEqual = (Core.Name "timesEqual")

_AugAssign_atEqual = (Core.Name "atEqual")

_AugAssign_slashEqual = (Core.Name "slashEqual")

_AugAssign_percentEqual = (Core.Name "percentEqual")

_AugAssign_ampersandEqual = (Core.Name "ampersandEqual")

_AugAssign_barEqual = (Core.Name "barEqual")

_AugAssign_caretEqual = (Core.Name "caretEqual")

_AugAssign_leftShiftEqual = (Core.Name "leftShiftEqual")

_AugAssign_rightShiftEqual = (Core.Name "rightShiftEqual")

_AugAssign_starStarEqual = (Core.Name "starStarEqual")

_AugAssign_doubleSlashEqual = (Core.Name "doubleSlashEqual")

newtype ReturnStatement = 
  ReturnStatement {
    unReturnStatement :: [StarExpression]}
  deriving (Eq, Ord, Read, Show)

_ReturnStatement = (Core.Name "hydra/ext/python/syntax.ReturnStatement")

newtype RaiseStatement = 
  RaiseStatement {
    unRaiseStatement :: (Maybe RaiseExpression)}
  deriving (Eq, Ord, Read, Show)

_RaiseStatement = (Core.Name "hydra/ext/python/syntax.RaiseStatement")

data RaiseExpression = 
  RaiseExpression {
    raiseExpressionExpression :: Expression,
    raiseExpressionFrom :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_RaiseExpression = (Core.Name "hydra/ext/python/syntax.RaiseExpression")

_RaiseExpression_expression = (Core.Name "expression")

_RaiseExpression_from = (Core.Name "from")

newtype DelStatement = 
  DelStatement {
    unDelStatement :: DelTargets}
  deriving (Eq, Ord, Read, Show)

_DelStatement = (Core.Name "hydra/ext/python/syntax.DelStatement")

newtype YieldStatement = 
  YieldStatement {
    unYieldStatement :: YieldExpression}
  deriving (Eq, Ord, Read, Show)

_YieldStatement = (Core.Name "hydra/ext/python/syntax.YieldStatement")

data AssertStatement = 
  AssertStatement {
    assertStatementExpression1 :: Expression,
    assertStatementExpression2 :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_AssertStatement = (Core.Name "hydra/ext/python/syntax.AssertStatement")

_AssertStatement_expression1 = (Core.Name "expression1")

_AssertStatement_expression2 = (Core.Name "expression2")

data ImportStatement = 
  ImportStatementName ImportName |
  ImportStatementFrom ImportFrom
  deriving (Eq, Ord, Read, Show)

_ImportStatement = (Core.Name "hydra/ext/python/syntax.ImportStatement")

_ImportStatement_name = (Core.Name "name")

_ImportStatement_from = (Core.Name "from")

newtype ImportName = 
  ImportName {
    unImportName :: [DottedAsName]}
  deriving (Eq, Ord, Read, Show)

_ImportName = (Core.Name "hydra/ext/python/syntax.ImportName")

data ImportFrom = 
  ImportFrom {
    importFromPrefixes :: [RelativeImportPrefix],
    importFromDottedName :: (Maybe DottedName),
    importFromTargets :: ImportFromTargets}
  deriving (Eq, Ord, Read, Show)

_ImportFrom = (Core.Name "hydra/ext/python/syntax.ImportFrom")

_ImportFrom_prefixes = (Core.Name "prefixes")

_ImportFrom_dottedName = (Core.Name "dottedName")

_ImportFrom_targets = (Core.Name "targets")

data RelativeImportPrefix = 
  RelativeImportPrefixDot  |
  RelativeImportPrefixEllipsis 
  deriving (Eq, Ord, Read, Show)

_RelativeImportPrefix = (Core.Name "hydra/ext/python/syntax.RelativeImportPrefix")

_RelativeImportPrefix_dot = (Core.Name "dot")

_RelativeImportPrefix_ellipsis = (Core.Name "ellipsis")

data ImportFromTargets = 
  ImportFromTargetsSimple [ImportFromAsName] |
  ImportFromTargetsParens [ImportFromAsName] |
  ImportFromTargetsStar 
  deriving (Eq, Ord, Read, Show)

_ImportFromTargets = (Core.Name "hydra/ext/python/syntax.ImportFromTargets")

_ImportFromTargets_simple = (Core.Name "simple")

_ImportFromTargets_parens = (Core.Name "parens")

_ImportFromTargets_star = (Core.Name "star")

data ImportFromAsName = 
  ImportFromAsName {
    importFromAsNameName :: Name,
    importFromAsNameAs :: (Maybe Name)}
  deriving (Eq, Ord, Read, Show)

_ImportFromAsName = (Core.Name "hydra/ext/python/syntax.ImportFromAsName")

_ImportFromAsName_name = (Core.Name "name")

_ImportFromAsName_as = (Core.Name "as")

data DottedAsName = 
  DottedAsName {
    dottedAsNameName :: DottedName,
    dottedAsNameAs :: (Maybe Name)}
  deriving (Eq, Ord, Read, Show)

_DottedAsName = (Core.Name "hydra/ext/python/syntax.DottedAsName")

_DottedAsName_name = (Core.Name "name")

_DottedAsName_as = (Core.Name "as")

newtype DottedName = 
  DottedName {
    unDottedName :: [Name]}
  deriving (Eq, Ord, Read, Show)

_DottedName = (Core.Name "hydra/ext/python/syntax.DottedName")

data Block = 
  BlockIndented [StatementWithComment] |
  BlockSimple [SimpleStatement]
  deriving (Eq, Ord, Read, Show)

_Block = (Core.Name "hydra/ext/python/syntax.Block")

_Block_indented = (Core.Name "indented")

_Block_simple = (Core.Name "simple")

newtype Decorators = 
  Decorators {
    unDecorators :: [NamedExpression]}
  deriving (Eq, Ord, Read, Show)

_Decorators = (Core.Name "hydra/ext/python/syntax.Decorators")

data ClassDefinition = 
  ClassDefinition {
    classDefinitionDecorators :: (Maybe Decorators),
    classDefinitionName :: Name,
    classDefinitionTypeParams :: [TypeParameter],
    classDefinitionArguments :: (Maybe Args),
    classDefinitionComment :: (Maybe String),
    classDefinitionBlock :: Block}
  deriving (Eq, Ord, Read, Show)

_ClassDefinition = (Core.Name "hydra/ext/python/syntax.ClassDefinition")

_ClassDefinition_decorators = (Core.Name "decorators")

_ClassDefinition_name = (Core.Name "name")

_ClassDefinition_typeParams = (Core.Name "typeParams")

_ClassDefinition_arguments = (Core.Name "arguments")

_ClassDefinition_comment = (Core.Name "comment")

_ClassDefinition_block = (Core.Name "block")

data FunctionDefinition = 
  FunctionDefinition {
    functionDefinitionDecorators :: (Maybe Decorators),
    functionDefinitionRaw :: FunctionDefRaw}
  deriving (Eq, Ord, Read, Show)

_FunctionDefinition = (Core.Name "hydra/ext/python/syntax.FunctionDefinition")

_FunctionDefinition_decorators = (Core.Name "decorators")

_FunctionDefinition_raw = (Core.Name "raw")

data FunctionDefRaw = 
  FunctionDefRaw {
    functionDefRawAsync :: Bool,
    functionDefRawName :: Name,
    functionDefRawTypeParams :: [TypeParameter],
    functionDefRawParams :: (Maybe Params),
    functionDefRawReturnType :: (Maybe Expression),
    functionDefRawFuncTypeComment :: (Maybe FuncTypeComment),
    functionDefRawBlock :: Block}
  deriving (Eq, Ord, Read, Show)

_FunctionDefRaw = (Core.Name "hydra/ext/python/syntax.FunctionDefRaw")

_FunctionDefRaw_async = (Core.Name "async")

_FunctionDefRaw_name = (Core.Name "name")

_FunctionDefRaw_typeParams = (Core.Name "typeParams")

_FunctionDefRaw_params = (Core.Name "params")

_FunctionDefRaw_returnType = (Core.Name "returnType")

_FunctionDefRaw_funcTypeComment = (Core.Name "funcTypeComment")

_FunctionDefRaw_block = (Core.Name "block")

newtype Params = 
  Params {
    unParams :: Parameters}
  deriving (Eq, Ord, Read, Show)

_Params = (Core.Name "hydra/ext/python/syntax.Params")

data Parameters = 
  ParametersSlashNoDefault SlashNoDefaultParameters |
  ParametersSlashWithDefault SlashWithDefaultParameters |
  ParametersParamNoDefault ParamNoDefaultParameters |
  ParametersParamWithDefault ParamWithDefaultParameters |
  ParametersStarEtc StarEtc
  deriving (Eq, Ord, Read, Show)

_Parameters = (Core.Name "hydra/ext/python/syntax.Parameters")

_Parameters_slashNoDefault = (Core.Name "slashNoDefault")

_Parameters_slashWithDefault = (Core.Name "slashWithDefault")

_Parameters_paramNoDefault = (Core.Name "paramNoDefault")

_Parameters_paramWithDefault = (Core.Name "paramWithDefault")

_Parameters_starEtc = (Core.Name "starEtc")

data SlashNoDefaultParameters = 
  SlashNoDefaultParameters {
    slashNoDefaultParametersSlash :: SlashNoDefault,
    slashNoDefaultParametersParamNoDefault :: [ParamNoDefault],
    slashNoDefaultParametersParamWithDefault :: [ParamWithDefault],
    slashNoDefaultParametersStarEtc :: (Maybe StarEtc)}
  deriving (Eq, Ord, Read, Show)

_SlashNoDefaultParameters = (Core.Name "hydra/ext/python/syntax.SlashNoDefaultParameters")

_SlashNoDefaultParameters_slash = (Core.Name "slash")

_SlashNoDefaultParameters_paramNoDefault = (Core.Name "paramNoDefault")

_SlashNoDefaultParameters_paramWithDefault = (Core.Name "paramWithDefault")

_SlashNoDefaultParameters_starEtc = (Core.Name "starEtc")

data SlashWithDefaultParameters = 
  SlashWithDefaultParameters {
    slashWithDefaultParametersParamNoDefault :: [ParamNoDefault],
    slashWithDefaultParametersParamWithDefault :: [ParamWithDefault],
    slashWithDefaultParametersStarEtc :: (Maybe StarEtc)}
  deriving (Eq, Ord, Read, Show)

_SlashWithDefaultParameters = (Core.Name "hydra/ext/python/syntax.SlashWithDefaultParameters")

_SlashWithDefaultParameters_paramNoDefault = (Core.Name "paramNoDefault")

_SlashWithDefaultParameters_paramWithDefault = (Core.Name "paramWithDefault")

_SlashWithDefaultParameters_starEtc = (Core.Name "starEtc")

data ParamNoDefaultParameters = 
  ParamNoDefaultParameters {
    paramNoDefaultParametersParamNoDefault :: [ParamNoDefault],
    paramNoDefaultParametersParamWithDefault :: [ParamWithDefault],
    paramNoDefaultParametersStarEtc :: (Maybe StarEtc)}
  deriving (Eq, Ord, Read, Show)

_ParamNoDefaultParameters = (Core.Name "hydra/ext/python/syntax.ParamNoDefaultParameters")

_ParamNoDefaultParameters_paramNoDefault = (Core.Name "paramNoDefault")

_ParamNoDefaultParameters_paramWithDefault = (Core.Name "paramWithDefault")

_ParamNoDefaultParameters_starEtc = (Core.Name "starEtc")

data ParamWithDefaultParameters = 
  ParamWithDefaultParameters {
    paramWithDefaultParametersParamWithDefault :: [ParamWithDefault],
    paramWithDefaultParametersStarEtc :: (Maybe StarEtc)}
  deriving (Eq, Ord, Read, Show)

_ParamWithDefaultParameters = (Core.Name "hydra/ext/python/syntax.ParamWithDefaultParameters")

_ParamWithDefaultParameters_paramWithDefault = (Core.Name "paramWithDefault")

_ParamWithDefaultParameters_starEtc = (Core.Name "starEtc")

newtype SlashNoDefault = 
  SlashNoDefault {
    unSlashNoDefault :: [ParamNoDefault]}
  deriving (Eq, Ord, Read, Show)

_SlashNoDefault = (Core.Name "hydra/ext/python/syntax.SlashNoDefault")

data SlashWithDefault = 
  SlashWithDefault {
    slashWithDefaultParamNoDefault :: [ParamNoDefault],
    slashWithDefaultParamWithDefault :: [ParamWithDefault]}
  deriving (Eq, Ord, Read, Show)

_SlashWithDefault = (Core.Name "hydra/ext/python/syntax.SlashWithDefault")

_SlashWithDefault_paramNoDefault = (Core.Name "paramNoDefault")

_SlashWithDefault_paramWithDefault = (Core.Name "paramWithDefault")

data StarEtc = 
  StarEtcStarNoDefault NoDefaultStarEtc |
  StarEtcStarNoDefaultStarAnnotation NoDefaultStarAnnotationStarEtc |
  StarEtcStarComma CommaStarEtc |
  StarEtcKeywords Keywords
  deriving (Eq, Ord, Read, Show)

_StarEtc = (Core.Name "hydra/ext/python/syntax.StarEtc")

_StarEtc_starNoDefault = (Core.Name "starNoDefault")

_StarEtc_starNoDefaultStarAnnotation = (Core.Name "starNoDefaultStarAnnotation")

_StarEtc_starComma = (Core.Name "starComma")

_StarEtc_keywords = (Core.Name "keywords")

data NoDefaultStarEtc = 
  NoDefaultStarEtc {
    noDefaultStarEtcParamNoDefault :: ParamNoDefault,
    noDefaultStarEtcParamMaybeDefault :: [ParamMaybeDefault],
    noDefaultStarEtcKeywords :: (Maybe Keywords)}
  deriving (Eq, Ord, Read, Show)

_NoDefaultStarEtc = (Core.Name "hydra/ext/python/syntax.NoDefaultStarEtc")

_NoDefaultStarEtc_paramNoDefault = (Core.Name "paramNoDefault")

_NoDefaultStarEtc_paramMaybeDefault = (Core.Name "paramMaybeDefault")

_NoDefaultStarEtc_keywords = (Core.Name "keywords")

data NoDefaultStarAnnotationStarEtc = 
  NoDefaultStarAnnotationStarEtc {
    noDefaultStarAnnotationStarEtcParamNoDefaultStarAnnotation :: ParamNoDefaultStarAnnotation,
    noDefaultStarAnnotationStarEtcParamMaybeDefault :: [ParamMaybeDefault],
    noDefaultStarAnnotationStarEtcKeywords :: (Maybe Keywords)}
  deriving (Eq, Ord, Read, Show)

_NoDefaultStarAnnotationStarEtc = (Core.Name "hydra/ext/python/syntax.NoDefaultStarAnnotationStarEtc")

_NoDefaultStarAnnotationStarEtc_paramNoDefaultStarAnnotation = (Core.Name "paramNoDefaultStarAnnotation")

_NoDefaultStarAnnotationStarEtc_paramMaybeDefault = (Core.Name "paramMaybeDefault")

_NoDefaultStarAnnotationStarEtc_keywords = (Core.Name "keywords")

data CommaStarEtc = 
  CommaStarEtc {
    commaStarEtcParamMaybeDefault :: [ParamMaybeDefault],
    commaStarEtcKeywords :: (Maybe Keywords)}
  deriving (Eq, Ord, Read, Show)

_CommaStarEtc = (Core.Name "hydra/ext/python/syntax.CommaStarEtc")

_CommaStarEtc_paramMaybeDefault = (Core.Name "paramMaybeDefault")

_CommaStarEtc_keywords = (Core.Name "keywords")

newtype Keywords = 
  Keywords {
    unKeywords :: ParamNoDefault}
  deriving (Eq, Ord, Read, Show)

_Keywords = (Core.Name "hydra/ext/python/syntax.Keywords")

data ParamNoDefault = 
  ParamNoDefault {
    paramNoDefaultParam :: Param,
    paramNoDefaultTypeComment :: (Maybe TypeComment)}
  deriving (Eq, Ord, Read, Show)

_ParamNoDefault = (Core.Name "hydra/ext/python/syntax.ParamNoDefault")

_ParamNoDefault_param = (Core.Name "param")

_ParamNoDefault_typeComment = (Core.Name "typeComment")

data ParamNoDefaultStarAnnotation = 
  ParamNoDefaultStarAnnotation {
    paramNoDefaultStarAnnotationParamStarAnnotation :: ParamStarAnnotation,
    paramNoDefaultStarAnnotationTypeComment :: (Maybe TypeComment)}
  deriving (Eq, Ord, Read, Show)

_ParamNoDefaultStarAnnotation = (Core.Name "hydra/ext/python/syntax.ParamNoDefaultStarAnnotation")

_ParamNoDefaultStarAnnotation_paramStarAnnotation = (Core.Name "paramStarAnnotation")

_ParamNoDefaultStarAnnotation_typeComment = (Core.Name "typeComment")

data ParamWithDefault = 
  ParamWithDefault {
    paramWithDefaultParam :: Param,
    paramWithDefaultDefault :: Default,
    paramWithDefaultTypeComment :: (Maybe TypeComment)}
  deriving (Eq, Ord, Read, Show)

_ParamWithDefault = (Core.Name "hydra/ext/python/syntax.ParamWithDefault")

_ParamWithDefault_param = (Core.Name "param")

_ParamWithDefault_default = (Core.Name "default")

_ParamWithDefault_typeComment = (Core.Name "typeComment")

data ParamMaybeDefault = 
  ParamMaybeDefault {
    paramMaybeDefaultParam :: Param,
    paramMaybeDefaultDefault :: (Maybe Default),
    paramMaybeDefaultTypeComment :: (Maybe TypeComment)}
  deriving (Eq, Ord, Read, Show)

_ParamMaybeDefault = (Core.Name "hydra/ext/python/syntax.ParamMaybeDefault")

_ParamMaybeDefault_param = (Core.Name "param")

_ParamMaybeDefault_default = (Core.Name "default")

_ParamMaybeDefault_typeComment = (Core.Name "typeComment")

data Param = 
  Param {
    paramName :: Name,
    paramAnnotation :: (Maybe Annotation)}
  deriving (Eq, Ord, Read, Show)

_Param = (Core.Name "hydra/ext/python/syntax.Param")

_Param_name = (Core.Name "name")

_Param_annotation = (Core.Name "annotation")

data ParamStarAnnotation = 
  ParamStarAnnotation {
    paramStarAnnotationName :: Name,
    paramStarAnnotationAnnotation :: StarAnnotation}
  deriving (Eq, Ord, Read, Show)

_ParamStarAnnotation = (Core.Name "hydra/ext/python/syntax.ParamStarAnnotation")

_ParamStarAnnotation_name = (Core.Name "name")

_ParamStarAnnotation_annotation = (Core.Name "annotation")

newtype Annotation = 
  Annotation {
    unAnnotation :: Expression}
  deriving (Eq, Ord, Read, Show)

_Annotation = (Core.Name "hydra/ext/python/syntax.Annotation")

newtype StarAnnotation = 
  StarAnnotation {
    unStarAnnotation :: StarExpression}
  deriving (Eq, Ord, Read, Show)

_StarAnnotation = (Core.Name "hydra/ext/python/syntax.StarAnnotation")

newtype Default = 
  Default {
    unDefault :: Expression}
  deriving (Eq, Ord, Read, Show)

_Default = (Core.Name "hydra/ext/python/syntax.Default")

data IfStatement = 
  IfStatement {
    ifStatementCondition :: NamedExpression,
    ifStatementBody :: Block,
    ifStatementContinuation :: (Maybe IfTail)}
  deriving (Eq, Ord, Read, Show)

_IfStatement = (Core.Name "hydra/ext/python/syntax.IfStatement")

_IfStatement_condition = (Core.Name "condition")

_IfStatement_body = (Core.Name "body")

_IfStatement_continuation = (Core.Name "continuation")

data IfTail = 
  IfTailElif IfStatement |
  IfTailElse Block
  deriving (Eq, Ord, Read, Show)

_IfTail = (Core.Name "hydra/ext/python/syntax.IfTail")

_IfTail_elif = (Core.Name "elif")

_IfTail_else = (Core.Name "else")

data WhileStatement = 
  WhileStatement {
    whileStatementCondition :: NamedExpression,
    whileStatementBody :: Block,
    whileStatementElse :: (Maybe Block)}
  deriving (Eq, Ord, Read, Show)

_WhileStatement = (Core.Name "hydra/ext/python/syntax.WhileStatement")

_WhileStatement_condition = (Core.Name "condition")

_WhileStatement_body = (Core.Name "body")

_WhileStatement_else = (Core.Name "else")

data ForStatement = 
  ForStatement {
    forStatementAsync :: Bool,
    forStatementTargets :: [StarTarget],
    forStatementExpressions :: [StarExpression],
    forStatementTypeComment :: (Maybe TypeComment),
    forStatementBody :: Block,
    forStatementElse :: (Maybe Block)}
  deriving (Eq, Ord, Read, Show)

_ForStatement = (Core.Name "hydra/ext/python/syntax.ForStatement")

_ForStatement_async = (Core.Name "async")

_ForStatement_targets = (Core.Name "targets")

_ForStatement_expressions = (Core.Name "expressions")

_ForStatement_typeComment = (Core.Name "typeComment")

_ForStatement_body = (Core.Name "body")

_ForStatement_else = (Core.Name "else")

data WithStatement = 
  WithStatement {
    withStatementAsync :: Bool,
    withStatementItems :: [WithItem],
    withStatementTypeComment :: (Maybe TypeComment),
    withStatementBody :: Block}
  deriving (Eq, Ord, Read, Show)

_WithStatement = (Core.Name "hydra/ext/python/syntax.WithStatement")

_WithStatement_async = (Core.Name "async")

_WithStatement_items = (Core.Name "items")

_WithStatement_typeComment = (Core.Name "typeComment")

_WithStatement_body = (Core.Name "body")

data WithItem = 
  WithItem {
    withItemExpression :: Expression,
    withItemAs :: (Maybe StarTarget)}
  deriving (Eq, Ord, Read, Show)

_WithItem = (Core.Name "hydra/ext/python/syntax.WithItem")

_WithItem_expression = (Core.Name "expression")

_WithItem_as = (Core.Name "as")

data TryStatement = 
  TryStatementFinally TryFinallyStatement |
  TryStatementExcept TryExceptStatement |
  TryStatementExceptStar TryExceptStarStatement
  deriving (Eq, Ord, Read, Show)

_TryStatement = (Core.Name "hydra/ext/python/syntax.TryStatement")

_TryStatement_finally = (Core.Name "finally")

_TryStatement_except = (Core.Name "except")

_TryStatement_exceptStar = (Core.Name "exceptStar")

data TryFinallyStatement = 
  TryFinallyStatement {
    tryFinallyStatementBody :: Block,
    tryFinallyStatementFinally :: Block}
  deriving (Eq, Ord, Read, Show)

_TryFinallyStatement = (Core.Name "hydra/ext/python/syntax.TryFinallyStatement")

_TryFinallyStatement_body = (Core.Name "body")

_TryFinallyStatement_finally = (Core.Name "finally")

data TryExceptStatement = 
  TryExceptStatement {
    tryExceptStatementBody :: Block,
    tryExceptStatementExcepts :: [ExceptBlock],
    tryExceptStatementElse :: (Maybe Block),
    tryExceptStatementFinally :: (Maybe Block)}
  deriving (Eq, Ord, Read, Show)

_TryExceptStatement = (Core.Name "hydra/ext/python/syntax.TryExceptStatement")

_TryExceptStatement_body = (Core.Name "body")

_TryExceptStatement_excepts = (Core.Name "excepts")

_TryExceptStatement_else = (Core.Name "else")

_TryExceptStatement_finally = (Core.Name "finally")

data TryExceptStarStatement = 
  TryExceptStarStatement {
    tryExceptStarStatementBody :: Block,
    tryExceptStarStatementExcepts :: [ExceptStarBlock],
    tryExceptStarStatementElse :: (Maybe Block),
    tryExceptStarStatementFinally :: (Maybe Block)}
  deriving (Eq, Ord, Read, Show)

_TryExceptStarStatement = (Core.Name "hydra/ext/python/syntax.TryExceptStarStatement")

_TryExceptStarStatement_body = (Core.Name "body")

_TryExceptStarStatement_excepts = (Core.Name "excepts")

_TryExceptStarStatement_else = (Core.Name "else")

_TryExceptStarStatement_finally = (Core.Name "finally")

data ExceptBlock = 
  ExceptBlock {
    exceptBlockExpression :: (Maybe ExceptExpression),
    exceptBlockBody :: Block}
  deriving (Eq, Ord, Read, Show)

_ExceptBlock = (Core.Name "hydra/ext/python/syntax.ExceptBlock")

_ExceptBlock_expression = (Core.Name "expression")

_ExceptBlock_body = (Core.Name "body")

data ExceptExpression = 
  ExceptExpression {
    exceptExpressionExpression :: Expression,
    exceptExpressionAs :: (Maybe Name)}
  deriving (Eq, Ord, Read, Show)

_ExceptExpression = (Core.Name "hydra/ext/python/syntax.ExceptExpression")

_ExceptExpression_expression = (Core.Name "expression")

_ExceptExpression_as = (Core.Name "as")

data ExceptStarBlock = 
  ExceptStarBlock {
    exceptStarBlockExpression :: Expression,
    exceptStarBlockAs :: (Maybe Name),
    exceptStarBlockBody :: Block}
  deriving (Eq, Ord, Read, Show)

_ExceptStarBlock = (Core.Name "hydra/ext/python/syntax.ExceptStarBlock")

_ExceptStarBlock_expression = (Core.Name "expression")

_ExceptStarBlock_as = (Core.Name "as")

_ExceptStarBlock_body = (Core.Name "body")

data MatchStatement = 
  MatchStatement {
    matchStatementSubject :: SubjectExpression,
    matchStatementCases :: [CaseBlock]}
  deriving (Eq, Ord, Read, Show)

_MatchStatement = (Core.Name "hydra/ext/python/syntax.MatchStatement")

_MatchStatement_subject = (Core.Name "subject")

_MatchStatement_cases = (Core.Name "cases")

data SubjectExpression = 
  SubjectExpressionTuple [StarNamedExpression] |
  SubjectExpressionExpression NamedExpression
  deriving (Eq, Ord, Read, Show)

_SubjectExpression = (Core.Name "hydra/ext/python/syntax.SubjectExpression")

_SubjectExpression_tuple = (Core.Name "tuple")

_SubjectExpression_expression = (Core.Name "expression")

data CaseBlock = 
  CaseBlock {
    caseBlockPatterns :: Patterns,
    caseBlockGuard :: (Maybe Guard),
    caseBlockBody :: Block}
  deriving (Eq, Ord, Read, Show)

_CaseBlock = (Core.Name "hydra/ext/python/syntax.CaseBlock")

_CaseBlock_patterns = (Core.Name "patterns")

_CaseBlock_guard = (Core.Name "guard")

_CaseBlock_body = (Core.Name "body")

newtype Guard = 
  Guard {
    unGuard :: NamedExpression}
  deriving (Eq, Ord, Read, Show)

_Guard = (Core.Name "hydra/ext/python/syntax.Guard")

data Patterns = 
  PatternsSequence OpenSequencePattern |
  PatternsPattern Pattern
  deriving (Eq, Ord, Read, Show)

_Patterns = (Core.Name "hydra/ext/python/syntax.Patterns")

_Patterns_sequence = (Core.Name "sequence")

_Patterns_pattern = (Core.Name "pattern")

data Pattern = 
  PatternAs AsPattern |
  PatternOr OrPattern
  deriving (Eq, Ord, Read, Show)

_Pattern = (Core.Name "hydra/ext/python/syntax.Pattern")

_Pattern_as = (Core.Name "as")

_Pattern_or = (Core.Name "or")

data AsPattern = 
  AsPattern {
    asPatternPattern :: OrPattern,
    asPatternAs :: PatternCaptureTarget}
  deriving (Eq, Ord, Read, Show)

_AsPattern = (Core.Name "hydra/ext/python/syntax.AsPattern")

_AsPattern_pattern = (Core.Name "pattern")

_AsPattern_as = (Core.Name "as")

newtype OrPattern = 
  OrPattern {
    unOrPattern :: [ClosedPattern]}
  deriving (Eq, Ord, Read, Show)

_OrPattern = (Core.Name "hydra/ext/python/syntax.OrPattern")

data ClosedPattern = 
  ClosedPatternLiteral LiteralExpression |
  ClosedPatternCapture CapturePattern |
  ClosedPatternWildcard  |
  ClosedPatternValue ValuePattern |
  ClosedPatternGroup GroupPattern |
  ClosedPatternSequence SequencePattern |
  ClosedPatternMapping MappingPattern |
  ClosedPatternClass ClassPattern
  deriving (Eq, Ord, Read, Show)

_ClosedPattern = (Core.Name "hydra/ext/python/syntax.ClosedPattern")

_ClosedPattern_literal = (Core.Name "literal")

_ClosedPattern_capture = (Core.Name "capture")

_ClosedPattern_wildcard = (Core.Name "wildcard")

_ClosedPattern_value = (Core.Name "value")

_ClosedPattern_group = (Core.Name "group")

_ClosedPattern_sequence = (Core.Name "sequence")

_ClosedPattern_mapping = (Core.Name "mapping")

_ClosedPattern_class = (Core.Name "class")

data LiteralExpression = 
  LiteralExpressionNumber SignedNumber |
  LiteralExpressionComplex ComplexNumber |
  LiteralExpressionString String |
  LiteralExpressionNone  |
  LiteralExpressionTrue  |
  LiteralExpressionFalse 
  deriving (Eq, Ord, Read, Show)

_LiteralExpression = (Core.Name "hydra/ext/python/syntax.LiteralExpression")

_LiteralExpression_number = (Core.Name "number")

_LiteralExpression_complex = (Core.Name "complex")

_LiteralExpression_string = (Core.Name "string")

_LiteralExpression_none = (Core.Name "none")

_LiteralExpression_true = (Core.Name "true")

_LiteralExpression_false = (Core.Name "false")

data ComplexNumber = 
  ComplexNumber {
    complexNumberReal :: SignedRealNumber,
    complexNumberPlusOrMinus :: PlusOrMinus,
    complexNumberImaginary :: ImaginaryNumber}
  deriving (Eq, Ord, Read, Show)

_ComplexNumber = (Core.Name "hydra/ext/python/syntax.ComplexNumber")

_ComplexNumber_real = (Core.Name "real")

_ComplexNumber_plusOrMinus = (Core.Name "plusOrMinus")

_ComplexNumber_imaginary = (Core.Name "imaginary")

data PlusOrMinus = 
  PlusOrMinusPlus  |
  PlusOrMinusMinus 
  deriving (Eq, Ord, Read, Show)

_PlusOrMinus = (Core.Name "hydra/ext/python/syntax.PlusOrMinus")

_PlusOrMinus_plus = (Core.Name "plus")

_PlusOrMinus_minus = (Core.Name "minus")

data SignedNumber = 
  SignedNumberSign PlusOrMinus |
  SignedNumberNumber Number
  deriving (Eq, Ord, Read, Show)

_SignedNumber = (Core.Name "hydra/ext/python/syntax.SignedNumber")

_SignedNumber_sign = (Core.Name "sign")

_SignedNumber_number = (Core.Name "number")

data SignedRealNumber = 
  SignedRealNumberSign PlusOrMinus |
  SignedRealNumberNumber RealNumber
  deriving (Eq, Ord, Read, Show)

_SignedRealNumber = (Core.Name "hydra/ext/python/syntax.SignedRealNumber")

_SignedRealNumber_sign = (Core.Name "sign")

_SignedRealNumber_number = (Core.Name "number")

newtype RealNumber = 
  RealNumber {
    unRealNumber :: Number}
  deriving (Eq, Ord, Read, Show)

_RealNumber = (Core.Name "hydra/ext/python/syntax.RealNumber")

newtype ImaginaryNumber = 
  ImaginaryNumber {
    unImaginaryNumber :: Number}
  deriving (Eq, Ord, Read, Show)

_ImaginaryNumber = (Core.Name "hydra/ext/python/syntax.ImaginaryNumber")

newtype CapturePattern = 
  CapturePattern {
    unCapturePattern :: PatternCaptureTarget}
  deriving (Eq, Ord, Read, Show)

_CapturePattern = (Core.Name "hydra/ext/python/syntax.CapturePattern")

newtype PatternCaptureTarget = 
  PatternCaptureTarget {
    unPatternCaptureTarget :: Name}
  deriving (Eq, Ord, Read, Show)

_PatternCaptureTarget = (Core.Name "hydra/ext/python/syntax.PatternCaptureTarget")

newtype ValuePattern = 
  ValuePattern {
    unValuePattern :: Attribute}
  deriving (Eq, Ord, Read, Show)

_ValuePattern = (Core.Name "hydra/ext/python/syntax.ValuePattern")

newtype Attribute = 
  Attribute {
    unAttribute :: [Name]}
  deriving (Eq, Ord, Read, Show)

_Attribute = (Core.Name "hydra/ext/python/syntax.Attribute")

newtype NameOrAttribute = 
  NameOrAttribute {
    unNameOrAttribute :: [Name]}
  deriving (Eq, Ord, Read, Show)

_NameOrAttribute = (Core.Name "hydra/ext/python/syntax.NameOrAttribute")

newtype GroupPattern = 
  GroupPattern {
    unGroupPattern :: Pattern}
  deriving (Eq, Ord, Read, Show)

_GroupPattern = (Core.Name "hydra/ext/python/syntax.GroupPattern")

data SequencePattern = 
  SequencePatternList (Maybe MaybeSequencePattern) |
  SequencePatternTuple (Maybe OpenSequencePattern)
  deriving (Eq, Ord, Read, Show)

_SequencePattern = (Core.Name "hydra/ext/python/syntax.SequencePattern")

_SequencePattern_list = (Core.Name "list")

_SequencePattern_tuple = (Core.Name "tuple")

data OpenSequencePattern = 
  OpenSequencePattern {
    openSequencePatternHead :: MaybeStarPattern,
    openSequencePatternTail :: (Maybe MaybeSequencePattern)}
  deriving (Eq, Ord, Read, Show)

_OpenSequencePattern = (Core.Name "hydra/ext/python/syntax.OpenSequencePattern")

_OpenSequencePattern_head = (Core.Name "head")

_OpenSequencePattern_tail = (Core.Name "tail")

newtype MaybeSequencePattern = 
  MaybeSequencePattern {
    unMaybeSequencePattern :: [MaybeStarPattern]}
  deriving (Eq, Ord, Read, Show)

_MaybeSequencePattern = (Core.Name "hydra/ext/python/syntax.MaybeSequencePattern")

data MaybeStarPattern = 
  MaybeStarPatternStar StarPattern |
  MaybeStarPatternPattern Pattern
  deriving (Eq, Ord, Read, Show)

_MaybeStarPattern = (Core.Name "hydra/ext/python/syntax.MaybeStarPattern")

_MaybeStarPattern_star = (Core.Name "star")

_MaybeStarPattern_pattern = (Core.Name "pattern")

data StarPattern = 
  StarPatternCapture PatternCaptureTarget |
  StarPatternWildcard 
  deriving (Eq, Ord, Read, Show)

_StarPattern = (Core.Name "hydra/ext/python/syntax.StarPattern")

_StarPattern_capture = (Core.Name "capture")

_StarPattern_wildcard = (Core.Name "wildcard")

data MappingPattern = 
  MappingPattern {
    mappingPatternItems :: (Maybe ItemsPattern),
    mappingPatternDoubleStar :: (Maybe DoubleStarPattern)}
  deriving (Eq, Ord, Read, Show)

_MappingPattern = (Core.Name "hydra/ext/python/syntax.MappingPattern")

_MappingPattern_items = (Core.Name "items")

_MappingPattern_doubleStar = (Core.Name "doubleStar")

newtype ItemsPattern = 
  ItemsPattern {
    unItemsPattern :: [KeyValuePattern]}
  deriving (Eq, Ord, Read, Show)

_ItemsPattern = (Core.Name "hydra/ext/python/syntax.ItemsPattern")

data KeyValuePattern = 
  KeyValuePattern {
    keyValuePatternKey :: LiteralExpressionOrAttribute,
    keyValuePatternValue :: Pattern}
  deriving (Eq, Ord, Read, Show)

_KeyValuePattern = (Core.Name "hydra/ext/python/syntax.KeyValuePattern")

_KeyValuePattern_key = (Core.Name "key")

_KeyValuePattern_value = (Core.Name "value")

data LiteralExpressionOrAttribute = 
  LiteralExpressionOrAttributeLiteral LiteralExpression |
  LiteralExpressionOrAttributeAttribute Attribute
  deriving (Eq, Ord, Read, Show)

_LiteralExpressionOrAttribute = (Core.Name "hydra/ext/python/syntax.LiteralExpressionOrAttribute")

_LiteralExpressionOrAttribute_literal = (Core.Name "literal")

_LiteralExpressionOrAttribute_attribute = (Core.Name "attribute")

newtype DoubleStarPattern = 
  DoubleStarPattern {
    unDoubleStarPattern :: PatternCaptureTarget}
  deriving (Eq, Ord, Read, Show)

_DoubleStarPattern = (Core.Name "hydra/ext/python/syntax.DoubleStarPattern")

data ClassPattern = 
  ClassPattern {
    classPatternNameOrAttribute :: NameOrAttribute,
    classPatternPositionalPatterns :: (Maybe PositionalPatterns),
    classPatternKeywordPatterns :: (Maybe KeywordPatterns)}
  deriving (Eq, Ord, Read, Show)

_ClassPattern = (Core.Name "hydra/ext/python/syntax.ClassPattern")

_ClassPattern_nameOrAttribute = (Core.Name "nameOrAttribute")

_ClassPattern_positionalPatterns = (Core.Name "positionalPatterns")

_ClassPattern_keywordPatterns = (Core.Name "keywordPatterns")

newtype PositionalPatterns = 
  PositionalPatterns {
    unPositionalPatterns :: [Pattern]}
  deriving (Eq, Ord, Read, Show)

_PositionalPatterns = (Core.Name "hydra/ext/python/syntax.PositionalPatterns")

newtype KeywordPatterns = 
  KeywordPatterns {
    unKeywordPatterns :: [KeywordPattern]}
  deriving (Eq, Ord, Read, Show)

_KeywordPatterns = (Core.Name "hydra/ext/python/syntax.KeywordPatterns")

data KeywordPattern = 
  KeywordPattern {
    keywordPatternName :: Name,
    keywordPatternPattern :: Pattern}
  deriving (Eq, Ord, Read, Show)

_KeywordPattern = (Core.Name "hydra/ext/python/syntax.KeywordPattern")

_KeywordPattern_name = (Core.Name "name")

_KeywordPattern_pattern = (Core.Name "pattern")

data TypeAlias = 
  TypeAlias {
    typeAliasName :: Name,
    typeAliasTypeParams :: [TypeParameter],
    typeAliasExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_TypeAlias = (Core.Name "hydra/ext/python/syntax.TypeAlias")

_TypeAlias_name = (Core.Name "name")

_TypeAlias_typeParams = (Core.Name "typeParams")

_TypeAlias_expression = (Core.Name "expression")

data TypeParameter = 
  TypeParameterSimple SimpleTypeParameter |
  TypeParameterStar StarTypeParameter |
  TypeParameterDoubleStar DoubleStarTypeParameter
  deriving (Eq, Ord, Read, Show)

_TypeParameter = (Core.Name "hydra/ext/python/syntax.TypeParameter")

_TypeParameter_simple = (Core.Name "simple")

_TypeParameter_star = (Core.Name "star")

_TypeParameter_doubleStar = (Core.Name "doubleStar")

data SimpleTypeParameter = 
  SimpleTypeParameter {
    simpleTypeParameterName :: Name,
    simpleTypeParameterBound :: (Maybe Expression),
    simpleTypeParameterDefault :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_SimpleTypeParameter = (Core.Name "hydra/ext/python/syntax.SimpleTypeParameter")

_SimpleTypeParameter_name = (Core.Name "name")

_SimpleTypeParameter_bound = (Core.Name "bound")

_SimpleTypeParameter_default = (Core.Name "default")

data StarTypeParameter = 
  StarTypeParameter {
    starTypeParameterName :: Name,
    starTypeParameterDefault :: (Maybe StarExpression)}
  deriving (Eq, Ord, Read, Show)

_StarTypeParameter = (Core.Name "hydra/ext/python/syntax.StarTypeParameter")

_StarTypeParameter_name = (Core.Name "name")

_StarTypeParameter_default = (Core.Name "default")

data DoubleStarTypeParameter = 
  DoubleStarTypeParameter {
    doubleStarTypeParameterName :: Name,
    doubleStarTypeParameterDefault :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_DoubleStarTypeParameter = (Core.Name "hydra/ext/python/syntax.DoubleStarTypeParameter")

_DoubleStarTypeParameter_name = (Core.Name "name")

_DoubleStarTypeParameter_default = (Core.Name "default")

data Expression = 
  ExpressionConditional Conditional |
  ExpressionSimple Disjunction |
  ExpressionLambda Lambda
  deriving (Eq, Ord, Read, Show)

_Expression = (Core.Name "hydra/ext/python/syntax.Expression")

_Expression_conditional = (Core.Name "conditional")

_Expression_simple = (Core.Name "simple")

_Expression_lambda = (Core.Name "lambda")

data Conditional = 
  Conditional {
    conditionalBody :: Disjunction,
    conditionalIf :: Disjunction,
    conditionalElse :: Expression}
  deriving (Eq, Ord, Read, Show)

_Conditional = (Core.Name "hydra/ext/python/syntax.Conditional")

_Conditional_body = (Core.Name "body")

_Conditional_if = (Core.Name "if")

_Conditional_else = (Core.Name "else")

data YieldExpression = 
  YieldExpressionFrom Expression |
  YieldExpressionSimple [StarExpression]
  deriving (Eq, Ord, Read, Show)

_YieldExpression = (Core.Name "hydra/ext/python/syntax.YieldExpression")

_YieldExpression_from = (Core.Name "from")

_YieldExpression_simple = (Core.Name "simple")

data StarExpression = 
  StarExpressionStar BitwiseOr |
  StarExpressionSimple Expression
  deriving (Eq, Ord, Read, Show)

_StarExpression = (Core.Name "hydra/ext/python/syntax.StarExpression")

_StarExpression_star = (Core.Name "star")

_StarExpression_simple = (Core.Name "simple")

newtype StarNamedExpressions = 
  StarNamedExpressions {
    unStarNamedExpressions :: [StarNamedExpression]}
  deriving (Eq, Ord, Read, Show)

_StarNamedExpressions = (Core.Name "hydra/ext/python/syntax.StarNamedExpressions")

data StarNamedExpression = 
  StarNamedExpressionStar BitwiseOr |
  StarNamedExpressionSimple NamedExpression
  deriving (Eq, Ord, Read, Show)

_StarNamedExpression = (Core.Name "hydra/ext/python/syntax.StarNamedExpression")

_StarNamedExpression_star = (Core.Name "star")

_StarNamedExpression_simple = (Core.Name "simple")

data AssignmentExpression = 
  AssignmentExpression {
    assignmentExpressionName :: Name,
    assignmentExpressionExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_AssignmentExpression = (Core.Name "hydra/ext/python/syntax.AssignmentExpression")

_AssignmentExpression_name = (Core.Name "name")

_AssignmentExpression_expression = (Core.Name "expression")

data NamedExpression = 
  NamedExpressionAssignment AssignmentExpression |
  NamedExpressionSimple Expression
  deriving (Eq, Ord, Read, Show)

_NamedExpression = (Core.Name "hydra/ext/python/syntax.NamedExpression")

_NamedExpression_assignment = (Core.Name "assignment")

_NamedExpression_simple = (Core.Name "simple")

newtype Disjunction = 
  Disjunction {
    unDisjunction :: [Conjunction]}
  deriving (Eq, Ord, Read, Show)

_Disjunction = (Core.Name "hydra/ext/python/syntax.Disjunction")

newtype Conjunction = 
  Conjunction {
    unConjunction :: [Inversion]}
  deriving (Eq, Ord, Read, Show)

_Conjunction = (Core.Name "hydra/ext/python/syntax.Conjunction")

data Inversion = 
  InversionNot Inversion |
  InversionSimple Comparison
  deriving (Eq, Ord, Read, Show)

_Inversion = (Core.Name "hydra/ext/python/syntax.Inversion")

_Inversion_not = (Core.Name "not")

_Inversion_simple = (Core.Name "simple")

data Comparison = 
  Comparison {
    comparisonLhs :: BitwiseOr,
    comparisonRhs :: [CompareOpBitwiseOrPair]}
  deriving (Eq, Ord, Read, Show)

_Comparison = (Core.Name "hydra/ext/python/syntax.Comparison")

_Comparison_lhs = (Core.Name "lhs")

_Comparison_rhs = (Core.Name "rhs")

data CompareOpBitwiseOrPair = 
  CompareOpBitwiseOrPair {
    compareOpBitwiseOrPairOperator :: CompareOp,
    compareOpBitwiseOrPairRhs :: BitwiseOr}
  deriving (Eq, Ord, Read, Show)

_CompareOpBitwiseOrPair = (Core.Name "hydra/ext/python/syntax.CompareOpBitwiseOrPair")

_CompareOpBitwiseOrPair_operator = (Core.Name "operator")

_CompareOpBitwiseOrPair_rhs = (Core.Name "rhs")

data CompareOp = 
  CompareOpEq  |
  CompareOpNoteq  |
  CompareOpLte  |
  CompareOpLt  |
  CompareOpGte  |
  CompareOpGt  |
  CompareOpNotin  |
  CompareOpIn  |
  CompareOpIsnot  |
  CompareOpIs 
  deriving (Eq, Ord, Read, Show)

_CompareOp = (Core.Name "hydra/ext/python/syntax.CompareOp")

_CompareOp_eq = (Core.Name "eq")

_CompareOp_noteq = (Core.Name "noteq")

_CompareOp_lte = (Core.Name "lte")

_CompareOp_lt = (Core.Name "lt")

_CompareOp_gte = (Core.Name "gte")

_CompareOp_gt = (Core.Name "gt")

_CompareOp_notin = (Core.Name "notin")

_CompareOp_in = (Core.Name "in")

_CompareOp_isnot = (Core.Name "isnot")

_CompareOp_is = (Core.Name "is")

data BitwiseOr = 
  BitwiseOr {
    bitwiseOrLhs :: (Maybe BitwiseOr),
    bitwiseOrRhs :: BitwiseXor}
  deriving (Eq, Ord, Read, Show)

_BitwiseOr = (Core.Name "hydra/ext/python/syntax.BitwiseOr")

_BitwiseOr_lhs = (Core.Name "lhs")

_BitwiseOr_rhs = (Core.Name "rhs")

data BitwiseXor = 
  BitwiseXor {
    bitwiseXorLhs :: (Maybe BitwiseXor),
    bitwiseXorRhs :: BitwiseAnd}
  deriving (Eq, Ord, Read, Show)

_BitwiseXor = (Core.Name "hydra/ext/python/syntax.BitwiseXor")

_BitwiseXor_lhs = (Core.Name "lhs")

_BitwiseXor_rhs = (Core.Name "rhs")

data BitwiseAnd = 
  BitwiseAnd {
    bitwiseAndLhs :: (Maybe BitwiseAnd),
    bitwiseAndRhs :: ShiftExpression}
  deriving (Eq, Ord, Read, Show)

_BitwiseAnd = (Core.Name "hydra/ext/python/syntax.BitwiseAnd")

_BitwiseAnd_lhs = (Core.Name "lhs")

_BitwiseAnd_rhs = (Core.Name "rhs")

data ShiftExpression = 
  ShiftExpression {
    shiftExpressionLhs :: (Maybe ShiftLhs),
    shiftExpressionRhs :: Sum}
  deriving (Eq, Ord, Read, Show)

_ShiftExpression = (Core.Name "hydra/ext/python/syntax.ShiftExpression")

_ShiftExpression_lhs = (Core.Name "lhs")

_ShiftExpression_rhs = (Core.Name "rhs")

data ShiftLhs = 
  ShiftLhs {
    shiftLhsOperand :: ShiftExpression,
    shiftLhsOperator :: ShiftOp}
  deriving (Eq, Ord, Read, Show)

_ShiftLhs = (Core.Name "hydra/ext/python/syntax.ShiftLhs")

_ShiftLhs_operand = (Core.Name "operand")

_ShiftLhs_operator = (Core.Name "operator")

data ShiftOp = 
  ShiftOpLeft  |
  ShiftOpRight 
  deriving (Eq, Ord, Read, Show)

_ShiftOp = (Core.Name "hydra/ext/python/syntax.ShiftOp")

_ShiftOp_left = (Core.Name "left")

_ShiftOp_right = (Core.Name "right")

data Sum = 
  Sum {
    sumLhs :: (Maybe SumLhs),
    sumRhs :: Term}
  deriving (Eq, Ord, Read, Show)

_Sum = (Core.Name "hydra/ext/python/syntax.Sum")

_Sum_lhs = (Core.Name "lhs")

_Sum_rhs = (Core.Name "rhs")

data SumLhs = 
  SumLhs {
    sumLhsOperand :: Sum,
    sumLhsOperator :: SumOp}
  deriving (Eq, Ord, Read, Show)

_SumLhs = (Core.Name "hydra/ext/python/syntax.SumLhs")

_SumLhs_operand = (Core.Name "operand")

_SumLhs_operator = (Core.Name "operator")

data SumOp = 
  SumOpAdd  |
  SumOpSub 
  deriving (Eq, Ord, Read, Show)

_SumOp = (Core.Name "hydra/ext/python/syntax.SumOp")

_SumOp_add = (Core.Name "add")

_SumOp_sub = (Core.Name "sub")

data Term = 
  Term {
    termLhs :: (Maybe TermLhs),
    termRhs :: Factor}
  deriving (Eq, Ord, Read, Show)

_Term = (Core.Name "hydra/ext/python/syntax.Term")

_Term_lhs = (Core.Name "lhs")

_Term_rhs = (Core.Name "rhs")

data TermLhs = 
  TermLhs {
    termLhsOperand :: Term,
    termLhsOperator :: TermOp}
  deriving (Eq, Ord, Read, Show)

_TermLhs = (Core.Name "hydra/ext/python/syntax.TermLhs")

_TermLhs_operand = (Core.Name "operand")

_TermLhs_operator = (Core.Name "operator")

data TermOp = 
  TermOpMul  |
  TermOpDiv  |
  TermOpFloordiv  |
  TermOpMod  |
  TermOpMatmul 
  deriving (Eq, Ord, Read, Show)

_TermOp = (Core.Name "hydra/ext/python/syntax.TermOp")

_TermOp_mul = (Core.Name "mul")

_TermOp_div = (Core.Name "div")

_TermOp_floordiv = (Core.Name "floordiv")

_TermOp_mod = (Core.Name "mod")

_TermOp_matmul = (Core.Name "matmul")

data Factor = 
  FactorPositive Factor |
  FactorNegative Factor |
  FactorComplement Factor |
  FactorSimple Power
  deriving (Eq, Ord, Read, Show)

_Factor = (Core.Name "hydra/ext/python/syntax.Factor")

_Factor_positive = (Core.Name "positive")

_Factor_negative = (Core.Name "negative")

_Factor_complement = (Core.Name "complement")

_Factor_simple = (Core.Name "simple")

data Power = 
  Power {
    powerLhs :: AwaitPrimary,
    powerRhs :: (Maybe Factor)}
  deriving (Eq, Ord, Read, Show)

_Power = (Core.Name "hydra/ext/python/syntax.Power")

_Power_lhs = (Core.Name "lhs")

_Power_rhs = (Core.Name "rhs")

data AwaitPrimary = 
  AwaitPrimary {
    awaitPrimaryAwait :: Bool,
    awaitPrimaryPrimary :: Primary}
  deriving (Eq, Ord, Read, Show)

_AwaitPrimary = (Core.Name "hydra/ext/python/syntax.AwaitPrimary")

_AwaitPrimary_await = (Core.Name "await")

_AwaitPrimary_primary = (Core.Name "primary")

data Primary = 
  PrimarySimple Atom |
  PrimaryCompound PrimaryWithRhs
  deriving (Eq, Ord, Read, Show)

_Primary = (Core.Name "hydra/ext/python/syntax.Primary")

_Primary_simple = (Core.Name "simple")

_Primary_compound = (Core.Name "compound")

data PrimaryWithRhs = 
  PrimaryWithRhs {
    primaryWithRhsPrimary :: Primary,
    primaryWithRhsRhs :: PrimaryRhs}
  deriving (Eq, Ord, Read, Show)

_PrimaryWithRhs = (Core.Name "hydra/ext/python/syntax.PrimaryWithRhs")

_PrimaryWithRhs_primary = (Core.Name "primary")

_PrimaryWithRhs_rhs = (Core.Name "rhs")

data PrimaryRhs = 
  PrimaryRhsProject Name |
  PrimaryRhsGenexp Genexp |
  PrimaryRhsCall Args |
  PrimaryRhsSlices Slices
  deriving (Eq, Ord, Read, Show)

_PrimaryRhs = (Core.Name "hydra/ext/python/syntax.PrimaryRhs")

_PrimaryRhs_project = (Core.Name "project")

_PrimaryRhs_genexp = (Core.Name "genexp")

_PrimaryRhs_call = (Core.Name "call")

_PrimaryRhs_slices = (Core.Name "slices")

data Slices = 
  Slices {
    slicesHead :: Slice,
    slicesTail :: [SliceOrStarredExpression]}
  deriving (Eq, Ord, Read, Show)

_Slices = (Core.Name "hydra/ext/python/syntax.Slices")

_Slices_head = (Core.Name "head")

_Slices_tail = (Core.Name "tail")

data SliceOrStarredExpression = 
  SliceOrStarredExpressionSlice Slice |
  SliceOrStarredExpressionStarred StarredExpression
  deriving (Eq, Ord, Read, Show)

_SliceOrStarredExpression = (Core.Name "hydra/ext/python/syntax.SliceOrStarredExpression")

_SliceOrStarredExpression_slice = (Core.Name "slice")

_SliceOrStarredExpression_starred = (Core.Name "starred")

data Slice = 
  SliceNamed NamedExpression |
  SliceSlice SliceExpression
  deriving (Eq, Ord, Read, Show)

_Slice = (Core.Name "hydra/ext/python/syntax.Slice")

_Slice_named = (Core.Name "named")

_Slice_slice = (Core.Name "slice")

data SliceExpression = 
  SliceExpression {
    sliceExpressionStart :: (Maybe Expression),
    sliceExpressionStop :: (Maybe Expression),
    sliceExpressionStep :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_SliceExpression = (Core.Name "hydra/ext/python/syntax.SliceExpression")

_SliceExpression_start = (Core.Name "start")

_SliceExpression_stop = (Core.Name "stop")

_SliceExpression_step = (Core.Name "step")

data Atom = 
  AtomName Name |
  AtomTrue  |
  AtomFalse  |
  AtomNone  |
  AtomString String |
  AtomNumber Number |
  AtomTuple Tuple |
  AtomGroup Group |
  AtomGenexp Genexp |
  AtomList List |
  AtomListcomp Listcomp |
  AtomDict Dict |
  AtomSet Set_ |
  AtomDictcomp Dictcomp |
  AtomSetcomp Setcomp |
  AtomEllipsis 
  deriving (Eq, Ord, Read, Show)

_Atom = (Core.Name "hydra/ext/python/syntax.Atom")

_Atom_name = (Core.Name "name")

_Atom_true = (Core.Name "true")

_Atom_false = (Core.Name "false")

_Atom_none = (Core.Name "none")

_Atom_string = (Core.Name "string")

_Atom_number = (Core.Name "number")

_Atom_tuple = (Core.Name "tuple")

_Atom_group = (Core.Name "group")

_Atom_genexp = (Core.Name "genexp")

_Atom_list = (Core.Name "list")

_Atom_listcomp = (Core.Name "listcomp")

_Atom_dict = (Core.Name "dict")

_Atom_set = (Core.Name "set")

_Atom_dictcomp = (Core.Name "dictcomp")

_Atom_setcomp = (Core.Name "setcomp")

_Atom_ellipsis = (Core.Name "ellipsis")

data Group = 
  GroupYield YieldExpression |
  GroupExpression NamedExpression
  deriving (Eq, Ord, Read, Show)

_Group = (Core.Name "hydra/ext/python/syntax.Group")

_Group_yield = (Core.Name "yield")

_Group_expression = (Core.Name "expression")

data Lambda = 
  Lambda {
    lambdaParams :: LambdaParameters,
    lambdaBody :: Expression}
  deriving (Eq, Ord, Read, Show)

_Lambda = (Core.Name "hydra/ext/python/syntax.Lambda")

_Lambda_params = (Core.Name "params")

_Lambda_body = (Core.Name "body")

data LambdaParameters = 
  LambdaParameters {
    lambdaParametersSlashNoDefault :: (Maybe LambdaSlashNoDefault),
    lambdaParametersParamNoDefault :: [LambdaParamNoDefault],
    lambdaParametersParamWithDefault :: [LambdaParamWithDefault],
    lambdaParametersStarEtc :: (Maybe LambdaStarEtc)}
  deriving (Eq, Ord, Read, Show)

_LambdaParameters = (Core.Name "hydra/ext/python/syntax.LambdaParameters")

_LambdaParameters_slashNoDefault = (Core.Name "slashNoDefault")

_LambdaParameters_paramNoDefault = (Core.Name "paramNoDefault")

_LambdaParameters_paramWithDefault = (Core.Name "paramWithDefault")

_LambdaParameters_starEtc = (Core.Name "starEtc")

data LambdaSlashNoDefault = 
  LambdaSlashNoDefault {
    lambdaSlashNoDefaultParameters :: [LambdaParamNoDefault]}
  deriving (Eq, Ord, Read, Show)

_LambdaSlashNoDefault = (Core.Name "hydra/ext/python/syntax.LambdaSlashNoDefault")

_LambdaSlashNoDefault_parameters = (Core.Name "parameters")

data LambdaSlashWithDefault = 
  LambdaSlashWithDefault {
    lambdaSlashWithDefaultParamNoDefault :: [LambdaParamNoDefault],
    lambdaSlashWithDefaultParamWithDefault :: [LambdaParamWithDefault]}
  deriving (Eq, Ord, Read, Show)

_LambdaSlashWithDefault = (Core.Name "hydra/ext/python/syntax.LambdaSlashWithDefault")

_LambdaSlashWithDefault_paramNoDefault = (Core.Name "paramNoDefault")

_LambdaSlashWithDefault_paramWithDefault = (Core.Name "paramWithDefault")

data LambdaStarEtc = 
  LambdaStarEtcStar Bool |
  LambdaStarEtcParamNoDefault (Maybe LambdaParamNoDefault) |
  LambdaStarEtcParamMaybeDefault [LambdaParamMaybeDefault] |
  LambdaStarEtcKwds LambdaKwds
  deriving (Eq, Ord, Read, Show)

_LambdaStarEtc = (Core.Name "hydra/ext/python/syntax.LambdaStarEtc")

_LambdaStarEtc_star = (Core.Name "star")

_LambdaStarEtc_paramNoDefault = (Core.Name "paramNoDefault")

_LambdaStarEtc_paramMaybeDefault = (Core.Name "paramMaybeDefault")

_LambdaStarEtc_kwds = (Core.Name "kwds")

newtype LambdaKwds = 
  LambdaKwds {
    unLambdaKwds :: LambdaParamNoDefault}
  deriving (Eq, Ord, Read, Show)

_LambdaKwds = (Core.Name "hydra/ext/python/syntax.LambdaKwds")

newtype LambdaParamNoDefault = 
  LambdaParamNoDefault {
    unLambdaParamNoDefault :: Name}
  deriving (Eq, Ord, Read, Show)

_LambdaParamNoDefault = (Core.Name "hydra/ext/python/syntax.LambdaParamNoDefault")

data LambdaParamWithDefault = 
  LambdaParamWithDefault {
    lambdaParamWithDefaultParam :: Name,
    lambdaParamWithDefaultDefault :: Default}
  deriving (Eq, Ord, Read, Show)

_LambdaParamWithDefault = (Core.Name "hydra/ext/python/syntax.LambdaParamWithDefault")

_LambdaParamWithDefault_param = (Core.Name "param")

_LambdaParamWithDefault_default = (Core.Name "default")

data LambdaParamMaybeDefault = 
  LambdaParamMaybeDefault {
    lambdaParamMaybeDefaultParam :: Name,
    lambdaParamMaybeDefaultDefault :: (Maybe Default)}
  deriving (Eq, Ord, Read, Show)

_LambdaParamMaybeDefault = (Core.Name "hydra/ext/python/syntax.LambdaParamMaybeDefault")

_LambdaParamMaybeDefault_param = (Core.Name "param")

_LambdaParamMaybeDefault_default = (Core.Name "default")

newtype List = 
  List {
    unList :: [StarNamedExpression]}
  deriving (Eq, Ord, Read, Show)

_List = (Core.Name "hydra/ext/python/syntax.List")

newtype Tuple = 
  Tuple {
    unTuple :: [StarNamedExpression]}
  deriving (Eq, Ord, Read, Show)

_Tuple = (Core.Name "hydra/ext/python/syntax.Tuple")

newtype Set_ = 
  Set_ {
    unSet :: [StarNamedExpression]}
  deriving (Eq, Ord, Read, Show)

_Set = (Core.Name "hydra/ext/python/syntax.Set")

newtype Dict = 
  Dict {
    unDict :: [DoubleStarredKvpairs]}
  deriving (Eq, Ord, Read, Show)

_Dict = (Core.Name "hydra/ext/python/syntax.Dict")

newtype DoubleStarredKvpairs = 
  DoubleStarredKvpairs {
    unDoubleStarredKvpairs :: [DoubleStarredKvpair]}
  deriving (Eq, Ord, Read, Show)

_DoubleStarredKvpairs = (Core.Name "hydra/ext/python/syntax.DoubleStarredKvpairs")

data DoubleStarredKvpair = 
  DoubleStarredKvpairStarred BitwiseOr |
  DoubleStarredKvpairKvpair Kvpair
  deriving (Eq, Ord, Read, Show)

_DoubleStarredKvpair = (Core.Name "hydra/ext/python/syntax.DoubleStarredKvpair")

_DoubleStarredKvpair_starred = (Core.Name "starred")

_DoubleStarredKvpair_kvpair = (Core.Name "kvpair")

data Kvpair = 
  Kvpair {
    kvpairKey :: Expression,
    kvpairValue :: Expression}
  deriving (Eq, Ord, Read, Show)

_Kvpair = (Core.Name "hydra/ext/python/syntax.Kvpair")

_Kvpair_key = (Core.Name "key")

_Kvpair_value = (Core.Name "value")

newtype ForIfClauses = 
  ForIfClauses {
    unForIfClauses :: [ForIfClause]}
  deriving (Eq, Ord, Read, Show)

_ForIfClauses = (Core.Name "hydra/ext/python/syntax.ForIfClauses")

data ForIfClause = 
  ForIfClause {
    forIfClauseAsync :: Bool,
    forIfClauseTargets :: [StarTarget],
    forIfClauseIn :: Disjunction,
    forIfClauseIfs :: [Disjunction]}
  deriving (Eq, Ord, Read, Show)

_ForIfClause = (Core.Name "hydra/ext/python/syntax.ForIfClause")

_ForIfClause_async = (Core.Name "async")

_ForIfClause_targets = (Core.Name "targets")

_ForIfClause_in = (Core.Name "in")

_ForIfClause_ifs = (Core.Name "ifs")

data Listcomp = 
  Listcomp {
    listcompExpression :: NamedExpression,
    listcompForIfClauses :: ForIfClauses}
  deriving (Eq, Ord, Read, Show)

_Listcomp = (Core.Name "hydra/ext/python/syntax.Listcomp")

_Listcomp_expression = (Core.Name "expression")

_Listcomp_forIfClauses = (Core.Name "forIfClauses")

data Setcomp = 
  Setcomp {
    setcompExpression :: NamedExpression,
    setcompForIfClauses :: ForIfClauses}
  deriving (Eq, Ord, Read, Show)

_Setcomp = (Core.Name "hydra/ext/python/syntax.Setcomp")

_Setcomp_expression = (Core.Name "expression")

_Setcomp_forIfClauses = (Core.Name "forIfClauses")

data Genexp = 
  Genexp {
    genexpHead :: GenexpHead,
    genexpTail :: ForIfClauses}
  deriving (Eq, Ord, Read, Show)

_Genexp = (Core.Name "hydra/ext/python/syntax.Genexp")

_Genexp_head = (Core.Name "head")

_Genexp_tail = (Core.Name "tail")

data GenexpHead = 
  GenexpHeadAssignment AssignmentExpression |
  GenexpHeadExpression Expression
  deriving (Eq, Ord, Read, Show)

_GenexpHead = (Core.Name "hydra/ext/python/syntax.GenexpHead")

_GenexpHead_assignment = (Core.Name "assignment")

_GenexpHead_expression = (Core.Name "expression")

data Dictcomp = 
  Dictcomp {
    dictcompKvpair :: Kvpair,
    dictcompForIfClauses :: ForIfClauses}
  deriving (Eq, Ord, Read, Show)

_Dictcomp = (Core.Name "hydra/ext/python/syntax.Dictcomp")

_Dictcomp_kvpair = (Core.Name "kvpair")

_Dictcomp_forIfClauses = (Core.Name "forIfClauses")

data Args = 
  Args {
    argsPositional :: [PosArg],
    argsKwargOrStarred :: [KwargOrStarred],
    argsKwargOrDoubleStarred :: [KwargOrDoubleStarred]}
  deriving (Eq, Ord, Read, Show)

_Args = (Core.Name "hydra/ext/python/syntax.Args")

_Args_positional = (Core.Name "positional")

_Args_kwargOrStarred = (Core.Name "kwargOrStarred")

_Args_kwargOrDoubleStarred = (Core.Name "kwargOrDoubleStarred")

data PosArg = 
  PosArgStarred StarredExpression |
  PosArgAssignment AssignmentExpression |
  PosArgExpression Expression
  deriving (Eq, Ord, Read, Show)

_PosArg = (Core.Name "hydra/ext/python/syntax.PosArg")

_PosArg_starred = (Core.Name "starred")

_PosArg_assignment = (Core.Name "assignment")

_PosArg_expression = (Core.Name "expression")

newtype StarredExpression = 
  StarredExpression {
    unStarredExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_StarredExpression = (Core.Name "hydra/ext/python/syntax.StarredExpression")

data KwargOrStarred = 
  KwargOrStarredKwarg Kwarg |
  KwargOrStarredStarred StarredExpression
  deriving (Eq, Ord, Read, Show)

_KwargOrStarred = (Core.Name "hydra/ext/python/syntax.KwargOrStarred")

_KwargOrStarred_kwarg = (Core.Name "kwarg")

_KwargOrStarred_starred = (Core.Name "starred")

data Kwarg = 
  Kwarg {
    kwargName :: Name,
    kwargValue :: Expression}
  deriving (Eq, Ord, Read, Show)

_Kwarg = (Core.Name "hydra/ext/python/syntax.Kwarg")

_Kwarg_name = (Core.Name "name")

_Kwarg_value = (Core.Name "value")

data KwargOrDoubleStarred = 
  KwargOrDoubleStarredKwarg Kwarg |
  KwargOrDoubleStarredDoubleStarred Expression
  deriving (Eq, Ord, Read, Show)

_KwargOrDoubleStarred = (Core.Name "hydra/ext/python/syntax.KwargOrDoubleStarred")

_KwargOrDoubleStarred_kwarg = (Core.Name "kwarg")

_KwargOrDoubleStarred_doubleStarred = (Core.Name "doubleStarred")

newtype StarTargetsListSeq = 
  StarTargetsListSeq {
    unStarTargetsListSeq :: [StarTarget]}
  deriving (Eq, Ord, Read, Show)

_StarTargetsListSeq = (Core.Name "hydra/ext/python/syntax.StarTargetsListSeq")

newtype StarTargetsTupleSeq = 
  StarTargetsTupleSeq {
    unStarTargetsTupleSeq :: [StarTarget]}
  deriving (Eq, Ord, Read, Show)

_StarTargetsTupleSeq = (Core.Name "hydra/ext/python/syntax.StarTargetsTupleSeq")

data StarTarget = 
  StarTargetStarred StarTarget |
  StarTargetUnstarred TargetWithStarAtom
  deriving (Eq, Ord, Read, Show)

_StarTarget = (Core.Name "hydra/ext/python/syntax.StarTarget")

_StarTarget_starred = (Core.Name "starred")

_StarTarget_unstarred = (Core.Name "unstarred")

data TargetWithStarAtom = 
  TargetWithStarAtomProject TPrimaryAndName |
  TargetWithStarAtomSlices TPrimaryAndSlices |
  TargetWithStarAtomAtom StarAtom
  deriving (Eq, Ord, Read, Show)

_TargetWithStarAtom = (Core.Name "hydra/ext/python/syntax.TargetWithStarAtom")

_TargetWithStarAtom_project = (Core.Name "project")

_TargetWithStarAtom_slices = (Core.Name "slices")

_TargetWithStarAtom_atom = (Core.Name "atom")

data TPrimaryAndName = 
  TPrimaryAndName {
    tPrimaryAndNamePrimary :: TPrimary,
    tPrimaryAndNameName :: Name}
  deriving (Eq, Ord, Read, Show)

_TPrimaryAndName = (Core.Name "hydra/ext/python/syntax.TPrimaryAndName")

_TPrimaryAndName_primary = (Core.Name "primary")

_TPrimaryAndName_name = (Core.Name "name")

data TPrimaryAndSlices = 
  TPrimaryAndSlices {
    tPrimaryAndSlicesPrimary :: TPrimary,
    tPrimaryAndSlicesSlices :: Slices}
  deriving (Eq, Ord, Read, Show)

_TPrimaryAndSlices = (Core.Name "hydra/ext/python/syntax.TPrimaryAndSlices")

_TPrimaryAndSlices_primary = (Core.Name "primary")

_TPrimaryAndSlices_slices = (Core.Name "slices")

data StarAtom = 
  StarAtomName Name |
  StarAtomTargetWithStarAtom TargetWithStarAtom |
  StarAtomStarTargetsTupleSeq (Maybe StarTargetsTupleSeq) |
  StarAtomStarTargetsListSeq (Maybe StarTargetsListSeq)
  deriving (Eq, Ord, Read, Show)

_StarAtom = (Core.Name "hydra/ext/python/syntax.StarAtom")

_StarAtom_name = (Core.Name "name")

_StarAtom_targetWithStarAtom = (Core.Name "targetWithStarAtom")

_StarAtom_starTargetsTupleSeq = (Core.Name "starTargetsTupleSeq")

_StarAtom_starTargetsListSeq = (Core.Name "starTargetsListSeq")

data SingleTarget = 
  SingleTargetSubscriptAttributeTarget SingleSubscriptAttributeTarget |
  SingleTargetName Name |
  SingleTargetParens SingleTarget
  deriving (Eq, Ord, Read, Show)

_SingleTarget = (Core.Name "hydra/ext/python/syntax.SingleTarget")

_SingleTarget_subscriptAttributeTarget = (Core.Name "subscriptAttributeTarget")

_SingleTarget_name = (Core.Name "name")

_SingleTarget_parens = (Core.Name "parens")

data SingleSubscriptAttributeTarget = 
  SingleSubscriptAttributeTargetPrimaryAndName TPrimaryAndName |
  SingleSubscriptAttributeTargetPrimaryAndSlices TPrimaryAndSlices
  deriving (Eq, Ord, Read, Show)

_SingleSubscriptAttributeTarget = (Core.Name "hydra/ext/python/syntax.SingleSubscriptAttributeTarget")

_SingleSubscriptAttributeTarget_primaryAndName = (Core.Name "primaryAndName")

_SingleSubscriptAttributeTarget_primaryAndSlices = (Core.Name "primaryAndSlices")

data TPrimary = 
  TPrimaryPrimaryAndName TPrimaryAndName |
  TPrimaryPrimaryAndSlices TPrimaryAndSlices |
  TPrimaryPrimaryAndGenexp TPrimaryAndGenexp |
  TPrimaryPrimaryAndArguments TPrimaryAndArguments |
  TPrimaryAtom Atom
  deriving (Eq, Ord, Read, Show)

_TPrimary = (Core.Name "hydra/ext/python/syntax.TPrimary")

_TPrimary_primaryAndName = (Core.Name "primaryAndName")

_TPrimary_primaryAndSlices = (Core.Name "primaryAndSlices")

_TPrimary_primaryAndGenexp = (Core.Name "primaryAndGenexp")

_TPrimary_primaryAndArguments = (Core.Name "primaryAndArguments")

_TPrimary_atom = (Core.Name "atom")

data TPrimaryAndGenexp = 
  TPrimaryAndGenexp {
    tPrimaryAndGenexpPrimary :: TPrimary,
    tPrimaryAndGenexpGenexp :: Genexp}
  deriving (Eq, Ord, Read, Show)

_TPrimaryAndGenexp = (Core.Name "hydra/ext/python/syntax.TPrimaryAndGenexp")

_TPrimaryAndGenexp_primary = (Core.Name "primary")

_TPrimaryAndGenexp_genexp = (Core.Name "genexp")

data TPrimaryAndArguments = 
  TPrimaryAndArguments {
    tPrimaryAndArgumentsPrimary :: TPrimary,
    tPrimaryAndArgumentsArguments :: (Maybe Args)}
  deriving (Eq, Ord, Read, Show)

_TPrimaryAndArguments = (Core.Name "hydra/ext/python/syntax.TPrimaryAndArguments")

_TPrimaryAndArguments_primary = (Core.Name "primary")

_TPrimaryAndArguments_arguments = (Core.Name "arguments")

newtype DelTargets = 
  DelTargets {
    unDelTargets :: [DelTarget]}
  deriving (Eq, Ord, Read, Show)

_DelTargets = (Core.Name "hydra/ext/python/syntax.DelTargets")

data DelTarget = 
  DelTargetPrimaryAndName TPrimaryAndName |
  DelTargetPrimaryAndSlices TPrimaryAndSlices |
  DelTargetDelTAtom DelTAtom
  deriving (Eq, Ord, Read, Show)

_DelTarget = (Core.Name "hydra/ext/python/syntax.DelTarget")

_DelTarget_primaryAndName = (Core.Name "primaryAndName")

_DelTarget_primaryAndSlices = (Core.Name "primaryAndSlices")

_DelTarget_delTAtom = (Core.Name "delTAtom")

data DelTAtom = 
  DelTAtomName Name |
  DelTAtomTarget DelTarget |
  DelTAtomTargets DelTargets
  deriving (Eq, Ord, Read, Show)

_DelTAtom = (Core.Name "hydra/ext/python/syntax.DelTAtom")

_DelTAtom_name = (Core.Name "name")

_DelTAtom_target = (Core.Name "target")

_DelTAtom_targets = (Core.Name "targets")

data TypeExpression = 
  TypeExpressionExpression Expression |
  TypeExpressionStarredExpression Expression |
  TypeExpressionDoubleStarredExpression Expression
  deriving (Eq, Ord, Read, Show)

_TypeExpression = (Core.Name "hydra/ext/python/syntax.TypeExpression")

_TypeExpression_expression = (Core.Name "expression")

_TypeExpression_starredExpression = (Core.Name "starredExpression")

_TypeExpression_doubleStarredExpression = (Core.Name "doubleStarredExpression")

newtype FuncTypeComment = 
  FuncTypeComment {
    unFuncTypeComment :: TypeComment}
  deriving (Eq, Ord, Read, Show)

_FuncTypeComment = (Core.Name "hydra/ext/python/syntax.FuncTypeComment")