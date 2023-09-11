-- | A Haskell syntax model, loosely based on Language.Haskell.Tools.AST

module Hydra.Langs.Haskell.Ast where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | A pattern-matching alternative
data Alternative = 
  Alternative {
    alternativePattern :: Pattern,
    alternativeRhs :: CaseRhs,
    alternativeBinds :: (Maybe LocalBindings)}
  deriving (Eq, Ord, Read, Show)

_Alternative = (Core.Name "hydra/langs/haskell/ast.Alternative")

_Alternative_pattern = (Core.FieldName "pattern")

_Alternative_rhs = (Core.FieldName "rhs")

_Alternative_binds = (Core.FieldName "binds")

-- | A type assertion
data Assertion = 
  AssertionClass Assertion_Class |
  AssertionTuple [Assertion]
  deriving (Eq, Ord, Read, Show)

_Assertion = (Core.Name "hydra/langs/haskell/ast.Assertion")

_Assertion_class = (Core.FieldName "class")

_Assertion_tuple = (Core.FieldName "tuple")

data Assertion_Class = 
  Assertion_Class {
    assertion_ClassName :: Name,
    assertion_ClassTypes :: [Type]}
  deriving (Eq, Ord, Read, Show)

_Assertion_Class = (Core.Name "hydra/langs/haskell/ast.Assertion.Class")

_Assertion_Class_name = (Core.FieldName "name")

_Assertion_Class_types = (Core.FieldName "types")

-- | The right-hand side of a pattern-matching alternative
newtype CaseRhs = 
  CaseRhs {
    -- | The right-hand side of a pattern-matching alternative
    unCaseRhs :: Expression}
  deriving (Eq, Ord, Read, Show)

_CaseRhs = (Core.Name "hydra/langs/haskell/ast.CaseRhs")

-- | A data constructor
data Constructor = 
  ConstructorOrdinary Constructor_Ordinary |
  ConstructorRecord Constructor_Record
  deriving (Eq, Ord, Read, Show)

_Constructor = (Core.Name "hydra/langs/haskell/ast.Constructor")

_Constructor_ordinary = (Core.FieldName "ordinary")

_Constructor_record = (Core.FieldName "record")

-- | An ordinary (positional) data constructor
data Constructor_Ordinary = 
  Constructor_Ordinary {
    constructor_OrdinaryName :: Name,
    constructor_OrdinaryFields :: [Type]}
  deriving (Eq, Ord, Read, Show)

_Constructor_Ordinary = (Core.Name "hydra/langs/haskell/ast.Constructor.Ordinary")

_Constructor_Ordinary_name = (Core.FieldName "name")

_Constructor_Ordinary_fields = (Core.FieldName "fields")

-- | A record-style data constructor
data Constructor_Record = 
  Constructor_Record {
    constructor_RecordName :: Name,
    constructor_RecordFields :: [FieldWithComments]}
  deriving (Eq, Ord, Read, Show)

_Constructor_Record = (Core.Name "hydra/langs/haskell/ast.Constructor.Record")

_Constructor_Record_name = (Core.FieldName "name")

_Constructor_Record_fields = (Core.FieldName "fields")

-- | A data constructor together with any comments
data ConstructorWithComments = 
  ConstructorWithComments {
    constructorWithCommentsBody :: Constructor,
    constructorWithCommentsComments :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_ConstructorWithComments = (Core.Name "hydra/langs/haskell/ast.ConstructorWithComments")

_ConstructorWithComments_body = (Core.FieldName "body")

_ConstructorWithComments_comments = (Core.FieldName "comments")

-- | A data type declaration
data DataDeclaration = 
  DataDeclaration {
    dataDeclarationKeyword :: DataDeclaration_Keyword,
    dataDeclarationContext :: [Assertion],
    dataDeclarationHead :: DeclarationHead,
    dataDeclarationConstructors :: [ConstructorWithComments],
    dataDeclarationDeriving :: [Deriving]}
  deriving (Eq, Ord, Read, Show)

_DataDeclaration = (Core.Name "hydra/langs/haskell/ast.DataDeclaration")

_DataDeclaration_keyword = (Core.FieldName "keyword")

_DataDeclaration_context = (Core.FieldName "context")

_DataDeclaration_head = (Core.FieldName "head")

_DataDeclaration_constructors = (Core.FieldName "constructors")

_DataDeclaration_deriving = (Core.FieldName "deriving")

-- | The 'data' versus 'newtype keyword
data DataDeclaration_Keyword = 
  DataDeclaration_KeywordData  |
  DataDeclaration_KeywordNewtype 
  deriving (Eq, Ord, Read, Show)

_DataDeclaration_Keyword = (Core.Name "hydra/langs/haskell/ast.DataDeclaration.Keyword")

_DataDeclaration_Keyword_data = (Core.FieldName "data")

_DataDeclaration_Keyword_newtype = (Core.FieldName "newtype")

-- | A data declaration together with any comments
data DeclarationWithComments = 
  DeclarationWithComments {
    declarationWithCommentsBody :: Declaration,
    declarationWithCommentsComments :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_DeclarationWithComments = (Core.Name "hydra/langs/haskell/ast.DeclarationWithComments")

_DeclarationWithComments_body = (Core.FieldName "body")

_DeclarationWithComments_comments = (Core.FieldName "comments")

-- | A data or value declaration
data Declaration = 
  DeclarationData DataDeclaration |
  DeclarationType TypeDeclaration |
  DeclarationValueBinding ValueBinding |
  DeclarationTypedBinding TypedBinding
  deriving (Eq, Ord, Read, Show)

_Declaration = (Core.Name "hydra/langs/haskell/ast.Declaration")

_Declaration_data = (Core.FieldName "data")

_Declaration_type = (Core.FieldName "type")

_Declaration_valueBinding = (Core.FieldName "valueBinding")

_Declaration_typedBinding = (Core.FieldName "typedBinding")

-- | The left-hand side of a declaration
data DeclarationHead = 
  DeclarationHeadApplication DeclarationHead_Application |
  DeclarationHeadParens DeclarationHead |
  DeclarationHeadSimple Name
  deriving (Eq, Ord, Read, Show)

_DeclarationHead = (Core.Name "hydra/langs/haskell/ast.DeclarationHead")

_DeclarationHead_application = (Core.FieldName "application")

_DeclarationHead_parens = (Core.FieldName "parens")

_DeclarationHead_simple = (Core.FieldName "simple")

-- | An application-style declaration head
data DeclarationHead_Application = 
  DeclarationHead_Application {
    declarationHead_ApplicationFunction :: DeclarationHead,
    declarationHead_ApplicationOperand :: Variable}
  deriving (Eq, Ord, Read, Show)

_DeclarationHead_Application = (Core.Name "hydra/langs/haskell/ast.DeclarationHead.Application")

_DeclarationHead_Application_function = (Core.FieldName "function")

_DeclarationHead_Application_operand = (Core.FieldName "operand")

-- | A 'deriving' statement
newtype Deriving = 
  Deriving {
    -- | A 'deriving' statement
    unDeriving :: [Name]}
  deriving (Eq, Ord, Read, Show)

_Deriving = (Core.Name "hydra/langs/haskell/ast.Deriving")

-- | An export statement
data Export = 
  ExportDeclaration ImportExportSpec |
  ExportModule ModuleName
  deriving (Eq, Ord, Read, Show)

_Export = (Core.Name "hydra/langs/haskell/ast.Export")

_Export_declaration = (Core.FieldName "declaration")

_Export_module = (Core.FieldName "module")

-- | A data expression
data Expression = 
  ExpressionApplication Expression_Application |
  ExpressionCase Expression_Case |
  ExpressionConstructRecord Expression_ConstructRecord |
  ExpressionDo [Statement] |
  ExpressionIf Expression_If |
  ExpressionInfixApplication Expression_InfixApplication |
  ExpressionLiteral Literal |
  ExpressionLambda Expression_Lambda |
  ExpressionLeftSection Expression_Section |
  ExpressionLet Expression_Let |
  ExpressionList [Expression] |
  ExpressionParens Expression |
  ExpressionPrefixApplication Expression_PrefixApplication |
  ExpressionRightSection Expression_Section |
  ExpressionTuple [Expression] |
  ExpressionTypeSignature Expression_TypeSignature |
  ExpressionUpdateRecord Expression_UpdateRecord |
  ExpressionVariable Name
  deriving (Eq, Ord, Read, Show)

_Expression = (Core.Name "hydra/langs/haskell/ast.Expression")

_Expression_application = (Core.FieldName "application")

_Expression_case = (Core.FieldName "case")

_Expression_constructRecord = (Core.FieldName "constructRecord")

_Expression_do = (Core.FieldName "do")

_Expression_if = (Core.FieldName "if")

_Expression_infixApplication = (Core.FieldName "infixApplication")

_Expression_literal = (Core.FieldName "literal")

_Expression_lambda = (Core.FieldName "lambda")

_Expression_leftSection = (Core.FieldName "leftSection")

_Expression_let = (Core.FieldName "let")

_Expression_list = (Core.FieldName "list")

_Expression_parens = (Core.FieldName "parens")

_Expression_prefixApplication = (Core.FieldName "prefixApplication")

_Expression_rightSection = (Core.FieldName "rightSection")

_Expression_tuple = (Core.FieldName "tuple")

_Expression_typeSignature = (Core.FieldName "typeSignature")

_Expression_updateRecord = (Core.FieldName "updateRecord")

_Expression_variable = (Core.FieldName "variable")

-- | An application expression
data Expression_Application = 
  Expression_Application {
    expression_ApplicationFunction :: Expression,
    expression_ApplicationArgument :: Expression}
  deriving (Eq, Ord, Read, Show)

_Expression_Application = (Core.Name "hydra/langs/haskell/ast.Expression.Application")

_Expression_Application_function = (Core.FieldName "function")

_Expression_Application_argument = (Core.FieldName "argument")

-- | A case expression
data Expression_Case = 
  Expression_Case {
    expression_CaseCase :: Expression,
    expression_CaseAlternatives :: [Alternative]}
  deriving (Eq, Ord, Read, Show)

_Expression_Case = (Core.Name "hydra/langs/haskell/ast.Expression.Case")

_Expression_Case_case = (Core.FieldName "case")

_Expression_Case_alternatives = (Core.FieldName "alternatives")

-- | A record constructor expression
data Expression_ConstructRecord = 
  Expression_ConstructRecord {
    expression_ConstructRecordName :: Name,
    expression_ConstructRecordFields :: [FieldUpdate]}
  deriving (Eq, Ord, Read, Show)

_Expression_ConstructRecord = (Core.Name "hydra/langs/haskell/ast.Expression.ConstructRecord")

_Expression_ConstructRecord_name = (Core.FieldName "name")

_Expression_ConstructRecord_fields = (Core.FieldName "fields")

-- | An 'if' expression
data Expression_If = 
  Expression_If {
    expression_IfCondition :: Expression,
    expression_IfThen :: Expression,
    expression_IfElse :: Expression}
  deriving (Eq, Ord, Read, Show)

_Expression_If = (Core.Name "hydra/langs/haskell/ast.Expression.If")

_Expression_If_condition = (Core.FieldName "condition")

_Expression_If_then = (Core.FieldName "then")

_Expression_If_else = (Core.FieldName "else")

-- | An infix application expression
data Expression_InfixApplication = 
  Expression_InfixApplication {
    expression_InfixApplicationLhs :: Expression,
    expression_InfixApplicationOperator :: Operator,
    expression_InfixApplicationRhs :: Expression}
  deriving (Eq, Ord, Read, Show)

_Expression_InfixApplication = (Core.Name "hydra/langs/haskell/ast.Expression.InfixApplication")

_Expression_InfixApplication_lhs = (Core.FieldName "lhs")

_Expression_InfixApplication_operator = (Core.FieldName "operator")

_Expression_InfixApplication_rhs = (Core.FieldName "rhs")

-- | A lambda expression
data Expression_Lambda = 
  Expression_Lambda {
    expression_LambdaBindings :: [Pattern],
    expression_LambdaInner :: Expression}
  deriving (Eq, Ord, Read, Show)

_Expression_Lambda = (Core.Name "hydra/langs/haskell/ast.Expression.Lambda")

_Expression_Lambda_bindings = (Core.FieldName "bindings")

_Expression_Lambda_inner = (Core.FieldName "inner")

-- | A 'let' expression
data Expression_Let = 
  Expression_Let {
    expression_LetBindings :: [LocalBinding],
    expression_LetInner :: Expression}
  deriving (Eq, Ord, Read, Show)

_Expression_Let = (Core.Name "hydra/langs/haskell/ast.Expression.Let")

_Expression_Let_bindings = (Core.FieldName "bindings")

_Expression_Let_inner = (Core.FieldName "inner")

-- | A prefix expression
data Expression_PrefixApplication = 
  Expression_PrefixApplication {
    expression_PrefixApplicationOperator :: Operator,
    expression_PrefixApplicationRhs :: Expression}
  deriving (Eq, Ord, Read, Show)

_Expression_PrefixApplication = (Core.Name "hydra/langs/haskell/ast.Expression.PrefixApplication")

_Expression_PrefixApplication_operator = (Core.FieldName "operator")

_Expression_PrefixApplication_rhs = (Core.FieldName "rhs")

-- | A section expression
data Expression_Section = 
  Expression_Section {
    expression_SectionOperator :: Operator,
    expression_SectionExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_Expression_Section = (Core.Name "hydra/langs/haskell/ast.Expression.Section")

_Expression_Section_operator = (Core.FieldName "operator")

_Expression_Section_expression = (Core.FieldName "expression")

-- | A type signature expression
data Expression_TypeSignature = 
  Expression_TypeSignature {
    expression_TypeSignatureInner :: Expression,
    expression_TypeSignatureType :: Type}
  deriving (Eq, Ord, Read, Show)

_Expression_TypeSignature = (Core.Name "hydra/langs/haskell/ast.Expression.TypeSignature")

_Expression_TypeSignature_inner = (Core.FieldName "inner")

_Expression_TypeSignature_type = (Core.FieldName "type")

-- | An update record expression
data Expression_UpdateRecord = 
  Expression_UpdateRecord {
    expression_UpdateRecordInner :: Expression,
    expression_UpdateRecordFields :: [FieldUpdate]}
  deriving (Eq, Ord, Read, Show)

_Expression_UpdateRecord = (Core.Name "hydra/langs/haskell/ast.Expression.UpdateRecord")

_Expression_UpdateRecord_inner = (Core.FieldName "inner")

_Expression_UpdateRecord_fields = (Core.FieldName "fields")

-- | A field (name/type pair)
data Field = 
  Field {
    fieldName :: Name,
    fieldType :: Type}
  deriving (Eq, Ord, Read, Show)

_Field = (Core.Name "hydra/langs/haskell/ast.Field")

_Field_name = (Core.FieldName "name")

_Field_type = (Core.FieldName "type")

-- | A field together with any comments
data FieldWithComments = 
  FieldWithComments {
    fieldWithCommentsField :: Field,
    fieldWithCommentsComments :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_FieldWithComments = (Core.Name "hydra/langs/haskell/ast.FieldWithComments")

_FieldWithComments_field = (Core.FieldName "field")

_FieldWithComments_comments = (Core.FieldName "comments")

-- | A field name and value
data FieldUpdate = 
  FieldUpdate {
    fieldUpdateName :: Name,
    fieldUpdateValue :: Expression}
  deriving (Eq, Ord, Read, Show)

_FieldUpdate = (Core.Name "hydra/langs/haskell/ast.FieldUpdate")

_FieldUpdate_name = (Core.FieldName "name")

_FieldUpdate_value = (Core.FieldName "value")

-- | An import statement
data Import = 
  Import {
    importQualified :: Bool,
    importModule :: ModuleName,
    importAs :: (Maybe ModuleName),
    importSpec :: (Maybe Import_Spec)}
  deriving (Eq, Ord, Read, Show)

_Import = (Core.Name "hydra/langs/haskell/ast.Import")

_Import_qualified = (Core.FieldName "qualified")

_Import_module = (Core.FieldName "module")

_Import_as = (Core.FieldName "as")

_Import_spec = (Core.FieldName "spec")

-- | An import specification
data Import_Spec = 
  Import_SpecList [ImportExportSpec] |
  Import_SpecHiding [ImportExportSpec]
  deriving (Eq, Ord, Read, Show)

_Import_Spec = (Core.Name "hydra/langs/haskell/ast.Import.Spec")

_Import_Spec_list = (Core.FieldName "list")

_Import_Spec_hiding = (Core.FieldName "hiding")

-- | An import modifier ('pattern' or 'type')
data ImportModifier = 
  ImportModifierPattern  |
  ImportModifierType 
  deriving (Eq, Ord, Read, Show)

_ImportModifier = (Core.Name "hydra/langs/haskell/ast.ImportModifier")

_ImportModifier_pattern = (Core.FieldName "pattern")

_ImportModifier_type = (Core.FieldName "type")

-- | An import or export specification
data ImportExportSpec = 
  ImportExportSpec {
    importExportSpecModifier :: (Maybe ImportModifier),
    importExportSpecName :: Name,
    importExportSpecSubspec :: (Maybe ImportExportSpec_Subspec)}
  deriving (Eq, Ord, Read, Show)

_ImportExportSpec = (Core.Name "hydra/langs/haskell/ast.ImportExportSpec")

_ImportExportSpec_modifier = (Core.FieldName "modifier")

_ImportExportSpec_name = (Core.FieldName "name")

_ImportExportSpec_subspec = (Core.FieldName "subspec")

data ImportExportSpec_Subspec = 
  ImportExportSpec_SubspecAll  |
  ImportExportSpec_SubspecList [Name]
  deriving (Eq, Ord, Read, Show)

_ImportExportSpec_Subspec = (Core.Name "hydra/langs/haskell/ast.ImportExportSpec.Subspec")

_ImportExportSpec_Subspec_all = (Core.FieldName "all")

_ImportExportSpec_Subspec_list = (Core.FieldName "list")

-- | A literal value
data Literal = 
  LiteralChar Int |
  LiteralDouble Double |
  LiteralFloat Float |
  LiteralInt Int |
  LiteralInteger Integer |
  LiteralString String
  deriving (Eq, Ord, Read, Show)

_Literal = (Core.Name "hydra/langs/haskell/ast.Literal")

_Literal_char = (Core.FieldName "char")

_Literal_double = (Core.FieldName "double")

_Literal_float = (Core.FieldName "float")

_Literal_int = (Core.FieldName "int")

_Literal_integer = (Core.FieldName "integer")

_Literal_string = (Core.FieldName "string")

data LocalBinding = 
  LocalBindingSignature TypeSignature |
  LocalBindingValue ValueBinding
  deriving (Eq, Ord, Read, Show)

_LocalBinding = (Core.Name "hydra/langs/haskell/ast.LocalBinding")

_LocalBinding_signature = (Core.FieldName "signature")

_LocalBinding_value = (Core.FieldName "value")

newtype LocalBindings = 
  LocalBindings {
    unLocalBindings :: [LocalBinding]}
  deriving (Eq, Ord, Read, Show)

_LocalBindings = (Core.Name "hydra/langs/haskell/ast.LocalBindings")

data Module = 
  Module {
    moduleHead :: (Maybe ModuleHead),
    moduleImports :: [Import],
    moduleDeclarations :: [DeclarationWithComments]}
  deriving (Eq, Ord, Read, Show)

_Module = (Core.Name "hydra/langs/haskell/ast.Module")

_Module_head = (Core.FieldName "head")

_Module_imports = (Core.FieldName "imports")

_Module_declarations = (Core.FieldName "declarations")

data ModuleHead = 
  ModuleHead {
    moduleHeadComments :: (Maybe String),
    moduleHeadName :: ModuleName,
    moduleHeadExports :: [Export]}
  deriving (Eq, Ord, Read, Show)

_ModuleHead = (Core.Name "hydra/langs/haskell/ast.ModuleHead")

_ModuleHead_comments = (Core.FieldName "comments")

_ModuleHead_name = (Core.FieldName "name")

_ModuleHead_exports = (Core.FieldName "exports")

newtype ModuleName = 
  ModuleName {
    unModuleName :: String}
  deriving (Eq, Ord, Read, Show)

_ModuleName = (Core.Name "hydra/langs/haskell/ast.ModuleName")

data Name = 
  NameImplicit QualifiedName |
  NameNormal QualifiedName |
  NameParens QualifiedName
  deriving (Eq, Ord, Read, Show)

_Name = (Core.Name "hydra/langs/haskell/ast.Name")

_Name_implicit = (Core.FieldName "implicit")

_Name_normal = (Core.FieldName "normal")

_Name_parens = (Core.FieldName "parens")

newtype NamePart = 
  NamePart {
    unNamePart :: String}
  deriving (Eq, Ord, Read, Show)

_NamePart = (Core.Name "hydra/langs/haskell/ast.NamePart")

data Operator = 
  OperatorBacktick QualifiedName |
  OperatorNormal QualifiedName
  deriving (Eq, Ord, Read, Show)

_Operator = (Core.Name "hydra/langs/haskell/ast.Operator")

_Operator_backtick = (Core.FieldName "backtick")

_Operator_normal = (Core.FieldName "normal")

data Pattern = 
  PatternApplication Pattern_Application |
  PatternAs Pattern_As |
  PatternList [Pattern] |
  PatternLiteral Literal |
  PatternName Name |
  PatternParens Pattern |
  PatternRecord Pattern_Record |
  PatternTuple [Pattern] |
  PatternTyped Pattern_Typed |
  PatternWildcard 
  deriving (Eq, Ord, Read, Show)

_Pattern = (Core.Name "hydra/langs/haskell/ast.Pattern")

_Pattern_application = (Core.FieldName "application")

_Pattern_as = (Core.FieldName "as")

_Pattern_list = (Core.FieldName "list")

_Pattern_literal = (Core.FieldName "literal")

_Pattern_name = (Core.FieldName "name")

_Pattern_parens = (Core.FieldName "parens")

_Pattern_record = (Core.FieldName "record")

_Pattern_tuple = (Core.FieldName "tuple")

_Pattern_typed = (Core.FieldName "typed")

_Pattern_wildcard = (Core.FieldName "wildcard")

data Pattern_Application = 
  Pattern_Application {
    pattern_ApplicationName :: Name,
    pattern_ApplicationArgs :: [Pattern]}
  deriving (Eq, Ord, Read, Show)

_Pattern_Application = (Core.Name "hydra/langs/haskell/ast.Pattern.Application")

_Pattern_Application_name = (Core.FieldName "name")

_Pattern_Application_args = (Core.FieldName "args")

data Pattern_As = 
  Pattern_As {
    pattern_AsName :: Name,
    pattern_AsInner :: Pattern}
  deriving (Eq, Ord, Read, Show)

_Pattern_As = (Core.Name "hydra/langs/haskell/ast.Pattern.As")

_Pattern_As_name = (Core.FieldName "name")

_Pattern_As_inner = (Core.FieldName "inner")

data Pattern_Record = 
  Pattern_Record {
    pattern_RecordName :: Name,
    pattern_RecordFields :: [PatternField]}
  deriving (Eq, Ord, Read, Show)

_Pattern_Record = (Core.Name "hydra/langs/haskell/ast.Pattern.Record")

_Pattern_Record_name = (Core.FieldName "name")

_Pattern_Record_fields = (Core.FieldName "fields")

data Pattern_Typed = 
  Pattern_Typed {
    pattern_TypedInner :: Pattern,
    pattern_TypedType :: Type}
  deriving (Eq, Ord, Read, Show)

_Pattern_Typed = (Core.Name "hydra/langs/haskell/ast.Pattern.Typed")

_Pattern_Typed_inner = (Core.FieldName "inner")

_Pattern_Typed_type = (Core.FieldName "type")

data PatternField = 
  PatternField {
    patternFieldName :: Name,
    patternFieldPattern :: Pattern}
  deriving (Eq, Ord, Read, Show)

_PatternField = (Core.Name "hydra/langs/haskell/ast.PatternField")

_PatternField_name = (Core.FieldName "name")

_PatternField_pattern = (Core.FieldName "pattern")

data QualifiedName = 
  QualifiedName {
    qualifiedNameQualifiers :: [NamePart],
    qualifiedNameUnqualified :: NamePart}
  deriving (Eq, Ord, Read, Show)

_QualifiedName = (Core.Name "hydra/langs/haskell/ast.QualifiedName")

_QualifiedName_qualifiers = (Core.FieldName "qualifiers")

_QualifiedName_unqualified = (Core.FieldName "unqualified")

newtype RightHandSide = 
  RightHandSide {
    unRightHandSide :: Expression}
  deriving (Eq, Ord, Read, Show)

_RightHandSide = (Core.Name "hydra/langs/haskell/ast.RightHandSide")

newtype Statement = 
  Statement {
    unStatement :: Expression}
  deriving (Eq, Ord, Read, Show)

_Statement = (Core.Name "hydra/langs/haskell/ast.Statement")

data Type = 
  TypeApplication Type_Application |
  TypeCtx Type_Context |
  TypeFunction Type_Function |
  TypeInfix Type_Infix |
  TypeList Type |
  TypeParens Type |
  TypeTuple [Type] |
  TypeVariable Name
  deriving (Eq, Ord, Read, Show)

_Type = (Core.Name "hydra/langs/haskell/ast.Type")

_Type_application = (Core.FieldName "application")

_Type_ctx = (Core.FieldName "ctx")

_Type_function = (Core.FieldName "function")

_Type_infix = (Core.FieldName "infix")

_Type_list = (Core.FieldName "list")

_Type_parens = (Core.FieldName "parens")

_Type_tuple = (Core.FieldName "tuple")

_Type_variable = (Core.FieldName "variable")

data Type_Application = 
  Type_Application {
    type_ApplicationContext :: Type,
    type_ApplicationArgument :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_Application = (Core.Name "hydra/langs/haskell/ast.Type.Application")

_Type_Application_context = (Core.FieldName "context")

_Type_Application_argument = (Core.FieldName "argument")

data Type_Context = 
  Type_Context {
    type_ContextCtx :: Assertion,
    type_ContextType :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_Context = (Core.Name "hydra/langs/haskell/ast.Type.Context")

_Type_Context_ctx = (Core.FieldName "ctx")

_Type_Context_type = (Core.FieldName "type")

data Type_Function = 
  Type_Function {
    type_FunctionDomain :: Type,
    type_FunctionCodomain :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_Function = (Core.Name "hydra/langs/haskell/ast.Type.Function")

_Type_Function_domain = (Core.FieldName "domain")

_Type_Function_codomain = (Core.FieldName "codomain")

data Type_Infix = 
  Type_Infix {
    type_InfixLhs :: Type,
    type_InfixOperator :: Operator,
    type_InfixRhs :: Operator}
  deriving (Eq, Ord, Read, Show)

_Type_Infix = (Core.Name "hydra/langs/haskell/ast.Type.Infix")

_Type_Infix_lhs = (Core.FieldName "lhs")

_Type_Infix_operator = (Core.FieldName "operator")

_Type_Infix_rhs = (Core.FieldName "rhs")

data TypeDeclaration = 
  TypeDeclaration {
    typeDeclarationName :: DeclarationHead,
    typeDeclarationType :: Type}
  deriving (Eq, Ord, Read, Show)

_TypeDeclaration = (Core.Name "hydra/langs/haskell/ast.TypeDeclaration")

_TypeDeclaration_name = (Core.FieldName "name")

_TypeDeclaration_type = (Core.FieldName "type")

data TypeSignature = 
  TypeSignature {
    typeSignatureName :: Name,
    typeSignatureType :: Type}
  deriving (Eq, Ord, Read, Show)

_TypeSignature = (Core.Name "hydra/langs/haskell/ast.TypeSignature")

_TypeSignature_name = (Core.FieldName "name")

_TypeSignature_type = (Core.FieldName "type")

data TypedBinding = 
  TypedBinding {
    typedBindingTypeSignature :: TypeSignature,
    typedBindingValueBinding :: ValueBinding}
  deriving (Eq, Ord, Read, Show)

_TypedBinding = (Core.Name "hydra/langs/haskell/ast.TypedBinding")

_TypedBinding_typeSignature = (Core.FieldName "typeSignature")

_TypedBinding_valueBinding = (Core.FieldName "valueBinding")

data ValueBinding = 
  ValueBindingSimple ValueBinding_Simple
  deriving (Eq, Ord, Read, Show)

_ValueBinding = (Core.Name "hydra/langs/haskell/ast.ValueBinding")

_ValueBinding_simple = (Core.FieldName "simple")

data ValueBinding_Simple = 
  ValueBinding_Simple {
    valueBinding_SimplePattern :: Pattern,
    valueBinding_SimpleRhs :: RightHandSide,
    valueBinding_SimpleLocalBindings :: (Maybe LocalBindings)}
  deriving (Eq, Ord, Read, Show)

_ValueBinding_Simple = (Core.Name "hydra/langs/haskell/ast.ValueBinding.Simple")

_ValueBinding_Simple_pattern = (Core.FieldName "pattern")

_ValueBinding_Simple_rhs = (Core.FieldName "rhs")

_ValueBinding_Simple_localBindings = (Core.FieldName "localBindings")

newtype Variable = 
  Variable {
    unVariable :: Name}
  deriving (Eq, Ord, Read, Show)

_Variable = (Core.Name "hydra/langs/haskell/ast.Variable")