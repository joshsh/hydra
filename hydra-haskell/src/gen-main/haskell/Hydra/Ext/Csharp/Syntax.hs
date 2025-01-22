-- | A C# syntax module based on the ANTLR grammar dated 02/07/2024 and available at:
-- |   https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/language-specification/grammar

module Hydra.Ext.Csharp.Syntax where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

newtype Identifier = 
  Identifier {
    unIdentifier :: String}
  deriving (Eq, Ord, Read, Show)

_Identifier = (Core.Name "hydra/ext/csharp/syntax.Identifier")

newtype Keyword = 
  Keyword {
    unKeyword :: String}
  deriving (Eq, Ord, Read, Show)

_Keyword = (Core.Name "hydra/ext/csharp/syntax.Keyword")

data Literal = 
  LiteralBoolean Bool |
  LiteralInteger IntegerLiteral |
  LiteralReal Double |
  LiteralCharacter String |
  LiteralString String |
  LiteralNull 
  deriving (Eq, Ord, Read, Show)

_Literal = (Core.Name "hydra/ext/csharp/syntax.Literal")

_Literal_boolean = (Core.Name "boolean")

_Literal_integer = (Core.Name "integer")

_Literal_real = (Core.Name "real")

_Literal_character = (Core.Name "character")

_Literal_string = (Core.Name "string")

_Literal_null = (Core.Name "null")

data IntegerLiteral = 
  IntegerLiteralDecimal String |
  IntegerLiteralHexadecimal String |
  IntegerLiteralBinary Integer
  deriving (Eq, Ord, Read, Show)

_IntegerLiteral = (Core.Name "hydra/ext/csharp/syntax.IntegerLiteral")

_IntegerLiteral_decimal = (Core.Name "decimal")

_IntegerLiteral_hexadecimal = (Core.Name "hexadecimal")

_IntegerLiteral_binary = (Core.Name "binary")

newtype NamespaceName = 
  NamespaceName {
    unNamespaceName :: NamespaceOrTypeName}
  deriving (Eq, Ord, Read, Show)

_NamespaceName = (Core.Name "hydra/ext/csharp/syntax.NamespaceName")

newtype TypeName = 
  TypeName {
    unTypeName :: NamespaceOrTypeName}
  deriving (Eq, Ord, Read, Show)

_TypeName = (Core.Name "hydra/ext/csharp/syntax.TypeName")

data NamespaceOrTypeName = 
  NamespaceOrTypeNameIdentifier IdentifierNamespaceOrTypeName |
  NamespaceOrTypeNameQualified QualifiedNamespaceOrTypeName |
  NamespaceOrTypeNameAlias QualifiedAliasMember
  deriving (Eq, Ord, Read, Show)

_NamespaceOrTypeName = (Core.Name "hydra/ext/csharp/syntax.NamespaceOrTypeName")

_NamespaceOrTypeName_identifier = (Core.Name "identifier")

_NamespaceOrTypeName_qualified = (Core.Name "qualified")

_NamespaceOrTypeName_alias = (Core.Name "alias")

data IdentifierNamespaceOrTypeName = 
  IdentifierNamespaceOrTypeName {
    identifierNamespaceOrTypeNameIdentifier :: Identifier,
    identifierNamespaceOrTypeNameArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_IdentifierNamespaceOrTypeName = (Core.Name "hydra/ext/csharp/syntax.IdentifierNamespaceOrTypeName")

_IdentifierNamespaceOrTypeName_identifier = (Core.Name "identifier")

_IdentifierNamespaceOrTypeName_arguments = (Core.Name "arguments")

data QualifiedNamespaceOrTypeName = 
  QualifiedNamespaceOrTypeName {
    qualifiedNamespaceOrTypeNameNamespaceOrType :: NamespaceOrTypeName,
    qualifiedNamespaceOrTypeNameIdentifier :: Identifier,
    qualifiedNamespaceOrTypeNameArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_QualifiedNamespaceOrTypeName = (Core.Name "hydra/ext/csharp/syntax.QualifiedNamespaceOrTypeName")

_QualifiedNamespaceOrTypeName_namespaceOrType = (Core.Name "namespaceOrType")

_QualifiedNamespaceOrTypeName_identifier = (Core.Name "identifier")

_QualifiedNamespaceOrTypeName_arguments = (Core.Name "arguments")

data Type = 
  TypeReference ReferenceType |
  TypeValue ValueType |
  TypeParam TypeParameter |
  TypePointer PointerType
  deriving (Eq, Ord, Read, Show)

_Type = (Core.Name "hydra/ext/csharp/syntax.Type")

_Type_reference = (Core.Name "reference")

_Type_value = (Core.Name "value")

_Type_param = (Core.Name "param")

_Type_pointer = (Core.Name "pointer")

data ReferenceType = 
  ReferenceTypeClass ClassType |
  ReferenceTypeInterface InterfaceType |
  ReferenceTypeArray ArrayType |
  ReferenceTypeDelegate DelegateType |
  ReferenceTypeDynamic 
  deriving (Eq, Ord, Read, Show)

_ReferenceType = (Core.Name "hydra/ext/csharp/syntax.ReferenceType")

_ReferenceType_class = (Core.Name "class")

_ReferenceType_interface = (Core.Name "interface")

_ReferenceType_array = (Core.Name "array")

_ReferenceType_delegate = (Core.Name "delegate")

_ReferenceType_dynamic = (Core.Name "dynamic")

data ClassType = 
  ClassTypeTypeName TypeName |
  ClassTypeObject  |
  ClassTypeString 
  deriving (Eq, Ord, Read, Show)

_ClassType = (Core.Name "hydra/ext/csharp/syntax.ClassType")

_ClassType_typeName = (Core.Name "typeName")

_ClassType_object = (Core.Name "object")

_ClassType_string = (Core.Name "string")

newtype InterfaceType = 
  InterfaceType {
    unInterfaceType :: TypeName}
  deriving (Eq, Ord, Read, Show)

_InterfaceType = (Core.Name "hydra/ext/csharp/syntax.InterfaceType")

data ArrayType = 
  ArrayType {
    arrayTypeType :: NonArrayType,
    arrayTypeRank :: [RankSpecifier]}
  deriving (Eq, Ord, Read, Show)

_ArrayType = (Core.Name "hydra/ext/csharp/syntax.ArrayType")

_ArrayType_type = (Core.Name "type")

_ArrayType_rank = (Core.Name "rank")

data NonArrayType = 
  NonArrayTypeValue ValueType |
  NonArrayTypeClass ClassType |
  NonArrayTypeInterface InterfaceType |
  NonArrayTypeDelegate DelegateType |
  NonArrayTypeDynamic  |
  NonArrayTypeParameter TypeParameter |
  NonArrayTypePointer PointerType
  deriving (Eq, Ord, Read, Show)

_NonArrayType = (Core.Name "hydra/ext/csharp/syntax.NonArrayType")

_NonArrayType_value = (Core.Name "value")

_NonArrayType_class = (Core.Name "class")

_NonArrayType_interface = (Core.Name "interface")

_NonArrayType_delegate = (Core.Name "delegate")

_NonArrayType_dynamic = (Core.Name "dynamic")

_NonArrayType_parameter = (Core.Name "parameter")

_NonArrayType_pointer = (Core.Name "pointer")

newtype RankSpecifier = 
  RankSpecifier {
    unRankSpecifier :: Int}
  deriving (Eq, Ord, Read, Show)

_RankSpecifier = (Core.Name "hydra/ext/csharp/syntax.RankSpecifier")

newtype DelegateType = 
  DelegateType {
    unDelegateType :: TypeName}
  deriving (Eq, Ord, Read, Show)

_DelegateType = (Core.Name "hydra/ext/csharp/syntax.DelegateType")

data ValueType = 
  ValueTypeNonNullable StructOrEnumType |
  ValueTypeNullable StructOrEnumType
  deriving (Eq, Ord, Read, Show)

_ValueType = (Core.Name "hydra/ext/csharp/syntax.ValueType")

_ValueType_nonNullable = (Core.Name "nonNullable")

_ValueType_nullable = (Core.Name "nullable")

data StructOrEnumType = 
  StructOrEnumTypeStruct StructType |
  StructOrEnumTypeEnum EnumType
  deriving (Eq, Ord, Read, Show)

_StructOrEnumType = (Core.Name "hydra/ext/csharp/syntax.StructOrEnumType")

_StructOrEnumType_struct = (Core.Name "struct")

_StructOrEnumType_enum = (Core.Name "enum")

data StructType = 
  StructTypeTypeName TypeName |
  StructTypeSimple SimpleType |
  StructTypeTuple TupleType
  deriving (Eq, Ord, Read, Show)

_StructType = (Core.Name "hydra/ext/csharp/syntax.StructType")

_StructType_typeName = (Core.Name "typeName")

_StructType_simple = (Core.Name "simple")

_StructType_tuple = (Core.Name "tuple")

data SimpleType = 
  SimpleTypeNumeric NumericType |
  SimpleTypeBool 
  deriving (Eq, Ord, Read, Show)

_SimpleType = (Core.Name "hydra/ext/csharp/syntax.SimpleType")

_SimpleType_numeric = (Core.Name "numeric")

_SimpleType_bool = (Core.Name "bool")

data NumericType = 
  NumericTypeIntegral IntegralType |
  NumericTypeFloatingPoint FloatingPointType |
  NumericTypeDecimal 
  deriving (Eq, Ord, Read, Show)

_NumericType = (Core.Name "hydra/ext/csharp/syntax.NumericType")

_NumericType_integral = (Core.Name "integral")

_NumericType_floatingPoint = (Core.Name "floatingPoint")

_NumericType_decimal = (Core.Name "decimal")

data IntegralType = 
  IntegralTypeSbyte  |
  IntegralTypeByte  |
  IntegralTypeShort  |
  IntegralTypeUshort  |
  IntegralTypeInt  |
  IntegralTypeUint  |
  IntegralTypeLong  |
  IntegralTypeUlong  |
  IntegralTypeChar 
  deriving (Eq, Ord, Read, Show)

_IntegralType = (Core.Name "hydra/ext/csharp/syntax.IntegralType")

_IntegralType_sbyte = (Core.Name "sbyte")

_IntegralType_byte = (Core.Name "byte")

_IntegralType_short = (Core.Name "short")

_IntegralType_ushort = (Core.Name "ushort")

_IntegralType_int = (Core.Name "int")

_IntegralType_uint = (Core.Name "uint")

_IntegralType_long = (Core.Name "long")

_IntegralType_ulong = (Core.Name "ulong")

_IntegralType_char = (Core.Name "char")

data FloatingPointType = 
  FloatingPointTypeFloat  |
  FloatingPointTypeDouble 
  deriving (Eq, Ord, Read, Show)

_FloatingPointType = (Core.Name "hydra/ext/csharp/syntax.FloatingPointType")

_FloatingPointType_float = (Core.Name "float")

_FloatingPointType_double = (Core.Name "double")

newtype TupleType = 
  TupleType {
    unTupleType :: [TupleTypeElement]}
  deriving (Eq, Ord, Read, Show)

_TupleType = (Core.Name "hydra/ext/csharp/syntax.TupleType")

data TupleTypeElement = 
  TupleTypeElement {
    tupleTypeElementType :: Type,
    tupleTypeElementIdentifier :: (Maybe Identifier)}
  deriving (Eq, Ord, Read, Show)

_TupleTypeElement = (Core.Name "hydra/ext/csharp/syntax.TupleTypeElement")

_TupleTypeElement_type = (Core.Name "type")

_TupleTypeElement_identifier = (Core.Name "identifier")

newtype EnumType = 
  EnumType {
    unEnumType :: TypeName}
  deriving (Eq, Ord, Read, Show)

_EnumType = (Core.Name "hydra/ext/csharp/syntax.EnumType")

newtype TypeArgumentList = 
  TypeArgumentList {
    unTypeArgumentList :: [Type]}
  deriving (Eq, Ord, Read, Show)

_TypeArgumentList = (Core.Name "hydra/ext/csharp/syntax.TypeArgumentList")

newtype TypeParameter = 
  TypeParameter {
    unTypeParameter :: Identifier}
  deriving (Eq, Ord, Read, Show)

_TypeParameter = (Core.Name "hydra/ext/csharp/syntax.TypeParameter")

data UnmanagedType = 
  UnmanagedTypeValue ValueType |
  UnmanagedTypePointer PointerType
  deriving (Eq, Ord, Read, Show)

_UnmanagedType = (Core.Name "hydra/ext/csharp/syntax.UnmanagedType")

_UnmanagedType_value = (Core.Name "value")

_UnmanagedType_pointer = (Core.Name "pointer")

newtype VariableReference = 
  VariableReference {
    unVariableReference :: Expression}
  deriving (Eq, Ord, Read, Show)

_VariableReference = (Core.Name "hydra/ext/csharp/syntax.VariableReference")

data Pattern = 
  PatternDeclaration DeclarationPattern |
  PatternConstant Expression |
  PatternVar Designation
  deriving (Eq, Ord, Read, Show)

_Pattern = (Core.Name "hydra/ext/csharp/syntax.Pattern")

_Pattern_declaration = (Core.Name "declaration")

_Pattern_constant = (Core.Name "constant")

_Pattern_var = (Core.Name "var")

data DeclarationPattern = 
  DeclarationPattern {
    declarationPatternType :: Type,
    declarationPatternDesignation :: Designation}
  deriving (Eq, Ord, Read, Show)

_DeclarationPattern = (Core.Name "hydra/ext/csharp/syntax.DeclarationPattern")

_DeclarationPattern_type = (Core.Name "type")

_DeclarationPattern_designation = (Core.Name "designation")

newtype Designation = 
  Designation {
    unDesignation :: Identifier}
  deriving (Eq, Ord, Read, Show)

_Designation = (Core.Name "hydra/ext/csharp/syntax.Designation")

newtype ArgumentList = 
  ArgumentList {
    unArgumentList :: [Argument]}
  deriving (Eq, Ord, Read, Show)

_ArgumentList = (Core.Name "hydra/ext/csharp/syntax.ArgumentList")

data Argument = 
  Argument {
    argumentName :: (Maybe Identifier),
    argumentValue :: ArgumentValue}
  deriving (Eq, Ord, Read, Show)

_Argument = (Core.Name "hydra/ext/csharp/syntax.Argument")

_Argument_name = (Core.Name "name")

_Argument_value = (Core.Name "value")

data ArgumentValue = 
  ArgumentValueExpression Expression |
  ArgumentValueIn VariableReference |
  ArgumentValueRef VariableReference |
  ArgumentValueOut VariableReference
  deriving (Eq, Ord, Read, Show)

_ArgumentValue = (Core.Name "hydra/ext/csharp/syntax.ArgumentValue")

_ArgumentValue_expression = (Core.Name "expression")

_ArgumentValue_in = (Core.Name "in")

_ArgumentValue_ref = (Core.Name "ref")

_ArgumentValue_out = (Core.Name "out")

data PrimaryExpression = 
  PrimaryExpressionNoArray PrimaryNoArrayCreationExpression |
  PrimaryExpressionArray ArrayCreationExpression
  deriving (Eq, Ord, Read, Show)

_PrimaryExpression = (Core.Name "hydra/ext/csharp/syntax.PrimaryExpression")

_PrimaryExpression_noArray = (Core.Name "noArray")

_PrimaryExpression_array = (Core.Name "array")

data PrimaryNoArrayCreationExpression = 
  PrimaryNoArrayCreationExpressionLiteral Literal |
  PrimaryNoArrayCreationExpressionInterpolatedString InterpolatedStringExpression |
  PrimaryNoArrayCreationExpressionSimpleName SimpleName |
  PrimaryNoArrayCreationExpressionParenthesized Expression |
  PrimaryNoArrayCreationExpressionTuple TupleExpression |
  PrimaryNoArrayCreationExpressionMemberAccess MemberAccess |
  PrimaryNoArrayCreationExpressionNullConditionalMemberAccess NullConditionalMemberAccess |
  PrimaryNoArrayCreationExpressionInvocation InvocationExpression |
  PrimaryNoArrayCreationExpressionElementAccess ElementAccess |
  PrimaryNoArrayCreationExpressionNullConditionalElementAccess NullConditionalElementAccess |
  PrimaryNoArrayCreationExpressionThisAccess  |
  PrimaryNoArrayCreationExpressionBaseAccess BaseAccess |
  PrimaryNoArrayCreationExpressionPostIncrement PrimaryExpression |
  PrimaryNoArrayCreationExpressionPostDecrement PrimaryExpression |
  PrimaryNoArrayCreationExpressionObjectCreation ObjectCreationExpression |
  PrimaryNoArrayCreationExpressionDelegateCreation DelegateCreationExpression |
  PrimaryNoArrayCreationExpressionAnonymousObjectCreation (Maybe MemberDeclaratorList) |
  PrimaryNoArrayCreationExpressionTypeof TypeofExpression |
  PrimaryNoArrayCreationExpressionSizeof UnmanagedType |
  PrimaryNoArrayCreationExpressionChecked Expression |
  PrimaryNoArrayCreationExpressionUnchecked Expression |
  PrimaryNoArrayCreationExpressionDefaultValue DefaultValueExpression |
  PrimaryNoArrayCreationExpressionNameof NamedEntity |
  PrimaryNoArrayCreationExpressionAnonymousMethod AnonymousMethodExpression |
  PrimaryNoArrayCreationExpressionPointerMemberAccess PointerMemberAccess |
  PrimaryNoArrayCreationExpressionPointerElementAccess PointerElementAccess |
  PrimaryNoArrayCreationExpressionStackalloc StackallocExpression
  deriving (Eq, Ord, Read, Show)

_PrimaryNoArrayCreationExpression = (Core.Name "hydra/ext/csharp/syntax.PrimaryNoArrayCreationExpression")

_PrimaryNoArrayCreationExpression_literal = (Core.Name "literal")

_PrimaryNoArrayCreationExpression_interpolatedString = (Core.Name "interpolatedString")

_PrimaryNoArrayCreationExpression_simpleName = (Core.Name "simpleName")

_PrimaryNoArrayCreationExpression_parenthesized = (Core.Name "parenthesized")

_PrimaryNoArrayCreationExpression_tuple = (Core.Name "tuple")

_PrimaryNoArrayCreationExpression_memberAccess = (Core.Name "memberAccess")

_PrimaryNoArrayCreationExpression_nullConditionalMemberAccess = (Core.Name "nullConditionalMemberAccess")

_PrimaryNoArrayCreationExpression_invocation = (Core.Name "invocation")

_PrimaryNoArrayCreationExpression_elementAccess = (Core.Name "elementAccess")

_PrimaryNoArrayCreationExpression_nullConditionalElementAccess = (Core.Name "nullConditionalElementAccess")

_PrimaryNoArrayCreationExpression_thisAccess = (Core.Name "thisAccess")

_PrimaryNoArrayCreationExpression_baseAccess = (Core.Name "baseAccess")

_PrimaryNoArrayCreationExpression_postIncrement = (Core.Name "postIncrement")

_PrimaryNoArrayCreationExpression_postDecrement = (Core.Name "postDecrement")

_PrimaryNoArrayCreationExpression_objectCreation = (Core.Name "objectCreation")

_PrimaryNoArrayCreationExpression_delegateCreation = (Core.Name "delegateCreation")

_PrimaryNoArrayCreationExpression_anonymousObjectCreation = (Core.Name "anonymousObjectCreation")

_PrimaryNoArrayCreationExpression_typeof = (Core.Name "typeof")

_PrimaryNoArrayCreationExpression_sizeof = (Core.Name "sizeof")

_PrimaryNoArrayCreationExpression_checked = (Core.Name "checked")

_PrimaryNoArrayCreationExpression_unchecked = (Core.Name "unchecked")

_PrimaryNoArrayCreationExpression_defaultValue = (Core.Name "defaultValue")

_PrimaryNoArrayCreationExpression_nameof = (Core.Name "nameof")

_PrimaryNoArrayCreationExpression_anonymousMethod = (Core.Name "anonymousMethod")

_PrimaryNoArrayCreationExpression_pointerMemberAccess = (Core.Name "pointerMemberAccess")

_PrimaryNoArrayCreationExpression_pointerElementAccess = (Core.Name "pointerElementAccess")

_PrimaryNoArrayCreationExpression_stackalloc = (Core.Name "stackalloc")

data InterpolatedStringExpression = 
  InterpolatedStringExpressionRegular InterpolatedRegularStringExpression |
  InterpolatedStringExpressionVerbatim InterpolatedVerbatimStringExpression
  deriving (Eq, Ord, Read, Show)

_InterpolatedStringExpression = (Core.Name "hydra/ext/csharp/syntax.InterpolatedStringExpression")

_InterpolatedStringExpression_regular = (Core.Name "regular")

_InterpolatedStringExpression_verbatim = (Core.Name "verbatim")

newtype InterpolatedRegularStringExpression = 
  InterpolatedRegularStringExpression {
    unInterpolatedRegularStringExpression :: String}
  deriving (Eq, Ord, Read, Show)

_InterpolatedRegularStringExpression = (Core.Name "hydra/ext/csharp/syntax.InterpolatedRegularStringExpression")

data RegularInterpolation = 
  RegularInterpolation {
    regularInterpolationExpression :: Expression,
    regularInterpolationWidth :: (Maybe Expression),
    regularInterpolationFormat :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_RegularInterpolation = (Core.Name "hydra/ext/csharp/syntax.RegularInterpolation")

_RegularInterpolation_expression = (Core.Name "expression")

_RegularInterpolation_width = (Core.Name "width")

_RegularInterpolation_format = (Core.Name "format")

newtype InterpolatedVerbatimStringExpression = 
  InterpolatedVerbatimStringExpression {
    unInterpolatedVerbatimStringExpression :: String}
  deriving (Eq, Ord, Read, Show)

_InterpolatedVerbatimStringExpression = (Core.Name "hydra/ext/csharp/syntax.InterpolatedVerbatimStringExpression")

data VerbatimInterpolation = 
  VerbatimInterpolation {
    verbatimInterpolationExpression :: Expression,
    verbatimInterpolationWidth :: (Maybe ConstantExpression),
    verbatimInterpolationFormat :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_VerbatimInterpolation = (Core.Name "hydra/ext/csharp/syntax.VerbatimInterpolation")

_VerbatimInterpolation_expression = (Core.Name "expression")

_VerbatimInterpolation_width = (Core.Name "width")

_VerbatimInterpolation_format = (Core.Name "format")

data SimpleName = 
  SimpleName {
    simpleNameIdentifier :: Identifier,
    simpleNameTypeArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_SimpleName = (Core.Name "hydra/ext/csharp/syntax.SimpleName")

_SimpleName_identifier = (Core.Name "identifier")

_SimpleName_typeArguments = (Core.Name "typeArguments")

data TupleExpression = 
  TupleExpressionElements [TupleElement] |
  TupleExpressionDeconstruction DeconstructionTuple
  deriving (Eq, Ord, Read, Show)

_TupleExpression = (Core.Name "hydra/ext/csharp/syntax.TupleExpression")

_TupleExpression_elements = (Core.Name "elements")

_TupleExpression_deconstruction = (Core.Name "deconstruction")

data TupleElement = 
  TupleElement {
    tupleElementName :: (Maybe Identifier),
    tupleElementExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_TupleElement = (Core.Name "hydra/ext/csharp/syntax.TupleElement")

_TupleElement_name = (Core.Name "name")

_TupleElement_expression = (Core.Name "expression")

newtype DeconstructionTuple = 
  DeconstructionTuple {
    unDeconstructionTuple :: [DeconstructionElement]}
  deriving (Eq, Ord, Read, Show)

_DeconstructionTuple = (Core.Name "hydra/ext/csharp/syntax.DeconstructionTuple")

data DeconstructionElement = 
  DeconstructionElementTuple DeconstructionTuple |
  DeconstructionElementIdentifier Identifier
  deriving (Eq, Ord, Read, Show)

_DeconstructionElement = (Core.Name "hydra/ext/csharp/syntax.DeconstructionElement")

_DeconstructionElement_tuple = (Core.Name "tuple")

_DeconstructionElement_identifier = (Core.Name "identifier")

data MemberAccess = 
  MemberAccess {
    memberAccessHead :: MemberAccessHead,
    memberAccessIdentifier :: Identifier,
    memberAccessTypeArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_MemberAccess = (Core.Name "hydra/ext/csharp/syntax.MemberAccess")

_MemberAccess_head = (Core.Name "head")

_MemberAccess_identifier = (Core.Name "identifier")

_MemberAccess_typeArguments = (Core.Name "typeArguments")

data MemberAccessHead = 
  MemberAccessHeadPrimary PrimaryExpression |
  MemberAccessHeadPredefined PredefinedType |
  MemberAccessHeadQualifiedAlias QualifiedAliasMember
  deriving (Eq, Ord, Read, Show)

_MemberAccessHead = (Core.Name "hydra/ext/csharp/syntax.MemberAccessHead")

_MemberAccessHead_primary = (Core.Name "primary")

_MemberAccessHead_predefined = (Core.Name "predefined")

_MemberAccessHead_qualifiedAlias = (Core.Name "qualifiedAlias")

data PredefinedType = 
  PredefinedTypeBool  |
  PredefinedTypeByte  |
  PredefinedTypeChar  |
  PredefinedTypeDecimal  |
  PredefinedTypeDouble  |
  PredefinedTypeFloat  |
  PredefinedTypeInt  |
  PredefinedTypeLong  |
  PredefinedTypeObject  |
  PredefinedTypeSbyte  |
  PredefinedTypeShort  |
  PredefinedTypeString  |
  PredefinedTypeUint  |
  PredefinedTypeUlong  |
  PredefinedTypeUshort 
  deriving (Eq, Ord, Read, Show)

_PredefinedType = (Core.Name "hydra/ext/csharp/syntax.PredefinedType")

_PredefinedType_bool = (Core.Name "bool")

_PredefinedType_byte = (Core.Name "byte")

_PredefinedType_char = (Core.Name "char")

_PredefinedType_decimal = (Core.Name "decimal")

_PredefinedType_double = (Core.Name "double")

_PredefinedType_float = (Core.Name "float")

_PredefinedType_int = (Core.Name "int")

_PredefinedType_long = (Core.Name "long")

_PredefinedType_object = (Core.Name "object")

_PredefinedType_sbyte = (Core.Name "sbyte")

_PredefinedType_short = (Core.Name "short")

_PredefinedType_string = (Core.Name "string")

_PredefinedType_uint = (Core.Name "uint")

_PredefinedType_ulong = (Core.Name "ulong")

_PredefinedType_ushort = (Core.Name "ushort")

data NullConditionalMemberAccess = 
  NullConditionalMemberAccess {
    nullConditionalMemberAccessExpression :: PrimaryExpression,
    nullConditionalMemberAccessIdentifier :: Identifier,
    nullConditionalMemberAccessTypeArguments :: (Maybe TypeArgumentList),
    nullConditionalMemberAccessDependentAccess :: [DependentAccess]}
  deriving (Eq, Ord, Read, Show)

_NullConditionalMemberAccess = (Core.Name "hydra/ext/csharp/syntax.NullConditionalMemberAccess")

_NullConditionalMemberAccess_expression = (Core.Name "expression")

_NullConditionalMemberAccess_identifier = (Core.Name "identifier")

_NullConditionalMemberAccess_typeArguments = (Core.Name "typeArguments")

_NullConditionalMemberAccess_dependentAccess = (Core.Name "dependentAccess")

data DependentAccess = 
  DependentAccessMemberAccess DependentAccessForMember |
  DependentAccessElementAccess ArgumentList |
  DependentAccessInvocation (Maybe ArgumentList)
  deriving (Eq, Ord, Read, Show)

_DependentAccess = (Core.Name "hydra/ext/csharp/syntax.DependentAccess")

_DependentAccess_memberAccess = (Core.Name "memberAccess")

_DependentAccess_elementAccess = (Core.Name "elementAccess")

_DependentAccess_invocation = (Core.Name "invocation")

data DependentAccessForMember = 
  DependentAccessForMember {
    dependentAccessForMemberIdentifier :: Identifier,
    dependentAccessForMemberTypeArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_DependentAccessForMember = (Core.Name "hydra/ext/csharp/syntax.DependentAccessForMember")

_DependentAccessForMember_identifier = (Core.Name "identifier")

_DependentAccessForMember_typeArguments = (Core.Name "typeArguments")

data NullConditionalProjectionInitializer = 
  NullConditionalProjectionInitializer {
    nullConditionalProjectionInitializerExpression :: PrimaryExpression,
    nullConditionalProjectionInitializerIdentifier :: Identifier,
    nullConditionalProjectionInitializerTypeArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_NullConditionalProjectionInitializer = (Core.Name "hydra/ext/csharp/syntax.NullConditionalProjectionInitializer")

_NullConditionalProjectionInitializer_expression = (Core.Name "expression")

_NullConditionalProjectionInitializer_identifier = (Core.Name "identifier")

_NullConditionalProjectionInitializer_typeArguments = (Core.Name "typeArguments")

data InvocationExpression = 
  InvocationExpression {
    invocationExpressionExpression :: PrimaryExpression,
    invocationExpressionArguments :: (Maybe ArgumentList)}
  deriving (Eq, Ord, Read, Show)

_InvocationExpression = (Core.Name "hydra/ext/csharp/syntax.InvocationExpression")

_InvocationExpression_expression = (Core.Name "expression")

_InvocationExpression_arguments = (Core.Name "arguments")

data NullConditionalInvocationExpression = 
  NullConditionalInvocationExpression {
    nullConditionalInvocationExpressionHead :: NullConditionalInvocationExpressionHead,
    nullConditionalInvocationExpressionArguments :: (Maybe ArgumentList)}
  deriving (Eq, Ord, Read, Show)

_NullConditionalInvocationExpression = (Core.Name "hydra/ext/csharp/syntax.NullConditionalInvocationExpression")

_NullConditionalInvocationExpression_head = (Core.Name "head")

_NullConditionalInvocationExpression_arguments = (Core.Name "arguments")

data NullConditionalInvocationExpressionHead = 
  NullConditionalInvocationExpressionHeadMember NullConditionalMemberAccess |
  NullConditionalInvocationExpressionHeadElement NullConditionalElementAccess
  deriving (Eq, Ord, Read, Show)

_NullConditionalInvocationExpressionHead = (Core.Name "hydra/ext/csharp/syntax.NullConditionalInvocationExpressionHead")

_NullConditionalInvocationExpressionHead_member = (Core.Name "member")

_NullConditionalInvocationExpressionHead_element = (Core.Name "element")

data ElementAccess = 
  ElementAccess {
    elementAccessExpression :: PrimaryNoArrayCreationExpression,
    elementAccessArguments :: ArgumentList}
  deriving (Eq, Ord, Read, Show)

_ElementAccess = (Core.Name "hydra/ext/csharp/syntax.ElementAccess")

_ElementAccess_expression = (Core.Name "expression")

_ElementAccess_arguments = (Core.Name "arguments")

data NullConditionalElementAccess = 
  NullConditionalElementAccess {
    nullConditionalElementAccessExpression :: PrimaryNoArrayCreationExpression,
    nullConditionalElementAccessArguments :: ArgumentList,
    nullConditionalElementAccessDependentAccess :: [DependentAccess]}
  deriving (Eq, Ord, Read, Show)

_NullConditionalElementAccess = (Core.Name "hydra/ext/csharp/syntax.NullConditionalElementAccess")

_NullConditionalElementAccess_expression = (Core.Name "expression")

_NullConditionalElementAccess_arguments = (Core.Name "arguments")

_NullConditionalElementAccess_dependentAccess = (Core.Name "dependentAccess")

data BaseAccess = 
  BaseAccessIdentifier BaseAccessWithIdentifier |
  BaseAccessArguments ArgumentList
  deriving (Eq, Ord, Read, Show)

_BaseAccess = (Core.Name "hydra/ext/csharp/syntax.BaseAccess")

_BaseAccess_identifier = (Core.Name "identifier")

_BaseAccess_arguments = (Core.Name "arguments")

data BaseAccessWithIdentifier = 
  BaseAccessWithIdentifier {
    baseAccessWithIdentifierIdentifier :: Identifier,
    baseAccessWithIdentifierTypeArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_BaseAccessWithIdentifier = (Core.Name "hydra/ext/csharp/syntax.BaseAccessWithIdentifier")

_BaseAccessWithIdentifier_identifier = (Core.Name "identifier")

_BaseAccessWithIdentifier_typeArguments = (Core.Name "typeArguments")

data ObjectCreationExpression = 
  ObjectCreationExpression {
    objectCreationExpressionType :: Type,
    objectCreationExpressionArguments :: (Maybe ArgumentList),
    objectCreationExpressionInitializer :: (Maybe ObjectOrCollectionInitializer)}
  deriving (Eq, Ord, Read, Show)

_ObjectCreationExpression = (Core.Name "hydra/ext/csharp/syntax.ObjectCreationExpression")

_ObjectCreationExpression_type = (Core.Name "type")

_ObjectCreationExpression_arguments = (Core.Name "arguments")

_ObjectCreationExpression_initializer = (Core.Name "initializer")

data ObjectOrCollectionInitializer = 
  ObjectOrCollectionInitializerObject [MemberInitializer] |
  ObjectOrCollectionInitializerCollection [ElementInitializer]
  deriving (Eq, Ord, Read, Show)

_ObjectOrCollectionInitializer = (Core.Name "hydra/ext/csharp/syntax.ObjectOrCollectionInitializer")

_ObjectOrCollectionInitializer_object = (Core.Name "object")

_ObjectOrCollectionInitializer_collection = (Core.Name "collection")

data MemberInitializer = 
  MemberInitializer {
    memberInitializerTarget :: InitializerTarget,
    memberInitializerValue :: InitializerValue}
  deriving (Eq, Ord, Read, Show)

_MemberInitializer = (Core.Name "hydra/ext/csharp/syntax.MemberInitializer")

_MemberInitializer_target = (Core.Name "target")

_MemberInitializer_value = (Core.Name "value")

data InitializerTarget = 
  InitializerTargetIdentifier Identifier |
  InitializerTargetArguments ArgumentList
  deriving (Eq, Ord, Read, Show)

_InitializerTarget = (Core.Name "hydra/ext/csharp/syntax.InitializerTarget")

_InitializerTarget_identifier = (Core.Name "identifier")

_InitializerTarget_arguments = (Core.Name "arguments")

data InitializerValue = 
  InitializerValueExpression Expression |
  InitializerValueObjectOrCollection ObjectOrCollectionInitializer
  deriving (Eq, Ord, Read, Show)

_InitializerValue = (Core.Name "hydra/ext/csharp/syntax.InitializerValue")

_InitializerValue_expression = (Core.Name "expression")

_InitializerValue_objectOrCollection = (Core.Name "objectOrCollection")

data ElementInitializer = 
  ElementInitializerSingle NonAssignmentExpression |
  ElementInitializerList ExpressionList
  deriving (Eq, Ord, Read, Show)

_ElementInitializer = (Core.Name "hydra/ext/csharp/syntax.ElementInitializer")

_ElementInitializer_single = (Core.Name "single")

_ElementInitializer_list = (Core.Name "list")

newtype ExpressionList = 
  ExpressionList {
    unExpressionList :: [Expression]}
  deriving (Eq, Ord, Read, Show)

_ExpressionList = (Core.Name "hydra/ext/csharp/syntax.ExpressionList")

data ArrayCreationExpression = 
  ArrayCreationExpressionNonArrayType NonArrayTypeArrayCreationExpression |
  ArrayCreationExpressionArrayType ArrayTypeArrayCreationExpression |
  ArrayCreationExpressionRankSpecifier RankSpecifierArrayCreationExpression
  deriving (Eq, Ord, Read, Show)

_ArrayCreationExpression = (Core.Name "hydra/ext/csharp/syntax.ArrayCreationExpression")

_ArrayCreationExpression_nonArrayType = (Core.Name "nonArrayType")

_ArrayCreationExpression_arrayType = (Core.Name "arrayType")

_ArrayCreationExpression_rankSpecifier = (Core.Name "rankSpecifier")

data NonArrayTypeArrayCreationExpression = 
  NonArrayTypeArrayCreationExpression {
    nonArrayTypeArrayCreationExpressionType :: NonArrayType,
    nonArrayTypeArrayCreationExpressionExpressions :: ExpressionList,
    nonArrayTypeArrayCreationExpressionRankSpecifiers :: [RankSpecifier],
    nonArrayTypeArrayCreationExpressionInitializer :: (Maybe ArrayInitializer)}
  deriving (Eq, Ord, Read, Show)

_NonArrayTypeArrayCreationExpression = (Core.Name "hydra/ext/csharp/syntax.NonArrayTypeArrayCreationExpression")

_NonArrayTypeArrayCreationExpression_type = (Core.Name "type")

_NonArrayTypeArrayCreationExpression_expressions = (Core.Name "expressions")

_NonArrayTypeArrayCreationExpression_rankSpecifiers = (Core.Name "rankSpecifiers")

_NonArrayTypeArrayCreationExpression_initializer = (Core.Name "initializer")

data ArrayTypeArrayCreationExpression = 
  ArrayTypeArrayCreationExpression {
    arrayTypeArrayCreationExpressionType :: ArrayType,
    arrayTypeArrayCreationExpressionInitializer :: ArrayInitializer}
  deriving (Eq, Ord, Read, Show)

_ArrayTypeArrayCreationExpression = (Core.Name "hydra/ext/csharp/syntax.ArrayTypeArrayCreationExpression")

_ArrayTypeArrayCreationExpression_type = (Core.Name "type")

_ArrayTypeArrayCreationExpression_initializer = (Core.Name "initializer")

data RankSpecifierArrayCreationExpression = 
  RankSpecifierArrayCreationExpression {
    rankSpecifierArrayCreationExpressionRankSpecifier :: RankSpecifier,
    rankSpecifierArrayCreationExpressionInitializer :: ArrayInitializer}
  deriving (Eq, Ord, Read, Show)

_RankSpecifierArrayCreationExpression = (Core.Name "hydra/ext/csharp/syntax.RankSpecifierArrayCreationExpression")

_RankSpecifierArrayCreationExpression_rankSpecifier = (Core.Name "rankSpecifier")

_RankSpecifierArrayCreationExpression_initializer = (Core.Name "initializer")

data DelegateCreationExpression = 
  DelegateCreationExpression {
    delegateCreationExpressionType :: DelegateType,
    delegateCreationExpressionExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_DelegateCreationExpression = (Core.Name "hydra/ext/csharp/syntax.DelegateCreationExpression")

_DelegateCreationExpression_type = (Core.Name "type")

_DelegateCreationExpression_expression = (Core.Name "expression")

newtype MemberDeclaratorList = 
  MemberDeclaratorList {
    unMemberDeclaratorList :: [MemberDeclarator]}
  deriving (Eq, Ord, Read, Show)

_MemberDeclaratorList = (Core.Name "hydra/ext/csharp/syntax.MemberDeclaratorList")

data MemberDeclarator = 
  MemberDeclaratorName SimpleName |
  MemberDeclaratorMemberAccess MemberAccess |
  MemberDeclaratorNullConditionalProjectionInitializer NullConditionalProjectionInitializer |
  MemberDeclaratorBaseAccess BaseAccess |
  MemberDeclaratorAssignment AssignmentMemberDeclarator
  deriving (Eq, Ord, Read, Show)

_MemberDeclarator = (Core.Name "hydra/ext/csharp/syntax.MemberDeclarator")

_MemberDeclarator_name = (Core.Name "name")

_MemberDeclarator_memberAccess = (Core.Name "memberAccess")

_MemberDeclarator_nullConditionalProjectionInitializer = (Core.Name "nullConditionalProjectionInitializer")

_MemberDeclarator_baseAccess = (Core.Name "baseAccess")

_MemberDeclarator_assignment = (Core.Name "assignment")

data AssignmentMemberDeclarator = 
  AssignmentMemberDeclarator {
    assignmentMemberDeclaratorIdentifier :: Identifier,
    assignmentMemberDeclaratorExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_AssignmentMemberDeclarator = (Core.Name "hydra/ext/csharp/syntax.AssignmentMemberDeclarator")

_AssignmentMemberDeclarator_identifier = (Core.Name "identifier")

_AssignmentMemberDeclarator_expression = (Core.Name "expression")

data TypeofExpression = 
  TypeofExpressionType Type |
  TypeofExpressionUnboundTypeName UnboundTypeName |
  TypeofExpressionVoid 
  deriving (Eq, Ord, Read, Show)

_TypeofExpression = (Core.Name "hydra/ext/csharp/syntax.TypeofExpression")

_TypeofExpression_type = (Core.Name "type")

_TypeofExpression_unboundTypeName = (Core.Name "unboundTypeName")

_TypeofExpression_void = (Core.Name "void")

newtype UnboundTypeName = 
  UnboundTypeName {
    unUnboundTypeName :: [UnboundTypeNamePart]}
  deriving (Eq, Ord, Read, Show)

_UnboundTypeName = (Core.Name "hydra/ext/csharp/syntax.UnboundTypeName")

data UnboundTypeNamePart = 
  UnboundTypeNamePart {
    unboundTypeNamePartIdentifier :: Identifier,
    unboundTypeNamePartAliased :: Bool,
    unboundTypeNamePartDimension :: (Maybe Int)}
  deriving (Eq, Ord, Read, Show)

_UnboundTypeNamePart = (Core.Name "hydra/ext/csharp/syntax.UnboundTypeNamePart")

_UnboundTypeNamePart_identifier = (Core.Name "identifier")

_UnboundTypeNamePart_aliased = (Core.Name "aliased")

_UnboundTypeNamePart_dimension = (Core.Name "dimension")

data DefaultValueExpression = 
  DefaultValueExpressionExplicitlyTyped Type |
  DefaultValueExpressionDefaultLiteral 
  deriving (Eq, Ord, Read, Show)

_DefaultValueExpression = (Core.Name "hydra/ext/csharp/syntax.DefaultValueExpression")

_DefaultValueExpression_explicitlyTyped = (Core.Name "explicitlyTyped")

_DefaultValueExpression_defaultLiteral = (Core.Name "defaultLiteral")

data StackallocExpression = 
  StackallocExpression {
    stackallocExpressionType :: (Maybe UnmanagedType),
    stackallocExpressionExpression :: (Maybe ConstantExpression),
    stackallocExpressionInitializer :: [Expression]}
  deriving (Eq, Ord, Read, Show)

_StackallocExpression = (Core.Name "hydra/ext/csharp/syntax.StackallocExpression")

_StackallocExpression_type = (Core.Name "type")

_StackallocExpression_expression = (Core.Name "expression")

_StackallocExpression_initializer = (Core.Name "initializer")

data NamedEntity = 
  NamedEntity {
    namedEntityTarget :: NamedEntityTarget,
    namedEntityParts :: [NamedEntityPart]}
  deriving (Eq, Ord, Read, Show)

_NamedEntity = (Core.Name "hydra/ext/csharp/syntax.NamedEntity")

_NamedEntity_target = (Core.Name "target")

_NamedEntity_parts = (Core.Name "parts")

data NamedEntityPart = 
  NamedEntityPart {
    namedEntityPartIdentifier :: Identifier,
    namedEntityPartTypeArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_NamedEntityPart = (Core.Name "hydra/ext/csharp/syntax.NamedEntityPart")

_NamedEntityPart_identifier = (Core.Name "identifier")

_NamedEntityPart_typeArguments = (Core.Name "typeArguments")

data NamedEntityTarget = 
  NamedEntityTargetName SimpleName |
  NamedEntityTargetThis  |
  NamedEntityTargetBase  |
  NamedEntityTargetPredefinedType PredefinedType |
  NamedEntityTargetQualifiedAliasMember QualifiedAliasMember
  deriving (Eq, Ord, Read, Show)

_NamedEntityTarget = (Core.Name "hydra/ext/csharp/syntax.NamedEntityTarget")

_NamedEntityTarget_name = (Core.Name "name")

_NamedEntityTarget_this = (Core.Name "this")

_NamedEntityTarget_base = (Core.Name "base")

_NamedEntityTarget_predefinedType = (Core.Name "predefinedType")

_NamedEntityTarget_qualifiedAliasMember = (Core.Name "qualifiedAliasMember")

data UnaryExpression = 
  UnaryExpressionPrimary PrimaryExpression |
  UnaryExpressionPlus UnaryExpression |
  UnaryExpressionMinus UnaryExpression |
  UnaryExpressionNot UnaryExpression |
  UnaryExpressionBitwiseComplement UnaryExpression |
  UnaryExpressionPreIncrement UnaryExpression |
  UnaryExpressionPreDecrement UnaryExpression |
  UnaryExpressionCast CastExpression |
  UnaryExpressionAwait UnaryExpression |
  UnaryExpressionPointerIndirection UnaryExpression |
  UnaryExpressionAddressOf UnaryExpression
  deriving (Eq, Ord, Read, Show)

_UnaryExpression = (Core.Name "hydra/ext/csharp/syntax.UnaryExpression")

_UnaryExpression_primary = (Core.Name "primary")

_UnaryExpression_plus = (Core.Name "plus")

_UnaryExpression_minus = (Core.Name "minus")

_UnaryExpression_not = (Core.Name "not")

_UnaryExpression_bitwiseComplement = (Core.Name "bitwiseComplement")

_UnaryExpression_preIncrement = (Core.Name "preIncrement")

_UnaryExpression_preDecrement = (Core.Name "preDecrement")

_UnaryExpression_cast = (Core.Name "cast")

_UnaryExpression_await = (Core.Name "await")

_UnaryExpression_pointerIndirection = (Core.Name "pointerIndirection")

_UnaryExpression_addressOf = (Core.Name "addressOf")

data CastExpression = 
  CastExpression {
    castExpressionType :: Type,
    castExpressionExpression :: UnaryExpression}
  deriving (Eq, Ord, Read, Show)

_CastExpression = (Core.Name "hydra/ext/csharp/syntax.CastExpression")

_CastExpression_type = (Core.Name "type")

_CastExpression_expression = (Core.Name "expression")

data MultiplicativeExpression = 
  MultiplicativeExpressionSimple UnaryExpression |
  MultiplicativeExpressionBinary BinaryMultiplicativeExpression
  deriving (Eq, Ord, Read, Show)

_MultiplicativeExpression = (Core.Name "hydra/ext/csharp/syntax.MultiplicativeExpression")

_MultiplicativeExpression_simple = (Core.Name "simple")

_MultiplicativeExpression_binary = (Core.Name "binary")

data BinaryMultiplicativeExpression = 
  BinaryMultiplicativeExpression {
    binaryMultiplicativeExpressionLeft :: MultiplicativeExpression,
    binaryMultiplicativeExpressionOperator :: MultiplicativeOperator,
    binaryMultiplicativeExpressionRight :: UnaryExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryMultiplicativeExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryMultiplicativeExpression")

_BinaryMultiplicativeExpression_left = (Core.Name "left")

_BinaryMultiplicativeExpression_operator = (Core.Name "operator")

_BinaryMultiplicativeExpression_right = (Core.Name "right")

data MultiplicativeOperator = 
  MultiplicativeOperatorTimes  |
  MultiplicativeOperatorDivide  |
  MultiplicativeOperatorModulo 
  deriving (Eq, Ord, Read, Show)

_MultiplicativeOperator = (Core.Name "hydra/ext/csharp/syntax.MultiplicativeOperator")

_MultiplicativeOperator_times = (Core.Name "times")

_MultiplicativeOperator_divide = (Core.Name "divide")

_MultiplicativeOperator_modulo = (Core.Name "modulo")

data AdditiveExpression = 
  AdditiveExpressionSimple MultiplicativeExpression |
  AdditiveExpressionBinary BinaryAdditiveExpression
  deriving (Eq, Ord, Read, Show)

_AdditiveExpression = (Core.Name "hydra/ext/csharp/syntax.AdditiveExpression")

_AdditiveExpression_simple = (Core.Name "simple")

_AdditiveExpression_binary = (Core.Name "binary")

data BinaryAdditiveExpression = 
  BinaryAdditiveExpression {
    binaryAdditiveExpressionLeft :: AdditiveExpression,
    binaryAdditiveExpressionOperator :: AdditiveOperator,
    binaryAdditiveExpressionRight :: MultiplicativeExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryAdditiveExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryAdditiveExpression")

_BinaryAdditiveExpression_left = (Core.Name "left")

_BinaryAdditiveExpression_operator = (Core.Name "operator")

_BinaryAdditiveExpression_right = (Core.Name "right")

data AdditiveOperator = 
  AdditiveOperatorPlus  |
  AdditiveOperatorMinus 
  deriving (Eq, Ord, Read, Show)

_AdditiveOperator = (Core.Name "hydra/ext/csharp/syntax.AdditiveOperator")

_AdditiveOperator_plus = (Core.Name "plus")

_AdditiveOperator_minus = (Core.Name "minus")

data ShiftExpression = 
  ShiftExpressionSimple AdditiveExpression |
  ShiftExpressionBinary BinaryShiftExpression
  deriving (Eq, Ord, Read, Show)

_ShiftExpression = (Core.Name "hydra/ext/csharp/syntax.ShiftExpression")

_ShiftExpression_simple = (Core.Name "simple")

_ShiftExpression_binary = (Core.Name "binary")

data BinaryShiftExpression = 
  BinaryShiftExpression {
    binaryShiftExpressionLeft :: ShiftExpression,
    binaryShiftExpressionOperator :: ShiftOperator,
    binaryShiftExpressionRight :: AdditiveExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryShiftExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryShiftExpression")

_BinaryShiftExpression_left = (Core.Name "left")

_BinaryShiftExpression_operator = (Core.Name "operator")

_BinaryShiftExpression_right = (Core.Name "right")

data ShiftOperator = 
  ShiftOperatorLeft  |
  ShiftOperatorRight 
  deriving (Eq, Ord, Read, Show)

_ShiftOperator = (Core.Name "hydra/ext/csharp/syntax.ShiftOperator")

_ShiftOperator_left = (Core.Name "left")

_ShiftOperator_right = (Core.Name "right")

data RelationalExpression = 
  RelationalExpressionSimple ShiftExpression |
  RelationalExpressionBinary BinaryRelationalExpression |
  RelationalExpressionIsType IsTypeExpression |
  RelationalExpressionIsPattern IsPatternExpression |
  RelationalExpressionAsType AsTypeExpression
  deriving (Eq, Ord, Read, Show)

_RelationalExpression = (Core.Name "hydra/ext/csharp/syntax.RelationalExpression")

_RelationalExpression_simple = (Core.Name "simple")

_RelationalExpression_binary = (Core.Name "binary")

_RelationalExpression_isType = (Core.Name "isType")

_RelationalExpression_isPattern = (Core.Name "isPattern")

_RelationalExpression_asType = (Core.Name "asType")

data BinaryRelationalExpression = 
  BinaryRelationalExpression {
    binaryRelationalExpressionLeft :: RelationalExpression,
    binaryRelationalExpressionOperator :: RelationalOperator,
    binaryRelationalExpressionRight :: ShiftExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryRelationalExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryRelationalExpression")

_BinaryRelationalExpression_left = (Core.Name "left")

_BinaryRelationalExpression_operator = (Core.Name "operator")

_BinaryRelationalExpression_right = (Core.Name "right")

data RelationalOperator = 
  RelationalOperatorLessThan  |
  RelationalOperatorGreaterThan  |
  RelationalOperatorLessThanOrEqual  |
  RelationalOperatorGreaterThanOrEqual 
  deriving (Eq, Ord, Read, Show)

_RelationalOperator = (Core.Name "hydra/ext/csharp/syntax.RelationalOperator")

_RelationalOperator_lessThan = (Core.Name "lessThan")

_RelationalOperator_greaterThan = (Core.Name "greaterThan")

_RelationalOperator_lessThanOrEqual = (Core.Name "lessThanOrEqual")

_RelationalOperator_greaterThanOrEqual = (Core.Name "greaterThanOrEqual")

data IsTypeExpression = 
  IsTypeExpression {
    isTypeExpressionExpression :: RelationalExpression,
    isTypeExpressionType :: Type}
  deriving (Eq, Ord, Read, Show)

_IsTypeExpression = (Core.Name "hydra/ext/csharp/syntax.IsTypeExpression")

_IsTypeExpression_expression = (Core.Name "expression")

_IsTypeExpression_type = (Core.Name "type")

data IsPatternExpression = 
  IsPatternExpression {
    isPatternExpressionExpression :: RelationalExpression,
    isPatternExpressionPattern :: Pattern}
  deriving (Eq, Ord, Read, Show)

_IsPatternExpression = (Core.Name "hydra/ext/csharp/syntax.IsPatternExpression")

_IsPatternExpression_expression = (Core.Name "expression")

_IsPatternExpression_pattern = (Core.Name "pattern")

data AsTypeExpression = 
  AsTypeExpression {
    asTypeExpressionExpression :: RelationalExpression,
    asTypeExpressionType :: Type}
  deriving (Eq, Ord, Read, Show)

_AsTypeExpression = (Core.Name "hydra/ext/csharp/syntax.AsTypeExpression")

_AsTypeExpression_expression = (Core.Name "expression")

_AsTypeExpression_type = (Core.Name "type")

data EqualityExpression = 
  EqualityExpressionSimple RelationalExpression |
  EqualityExpressionBinary BinaryEqualityExpression
  deriving (Eq, Ord, Read, Show)

_EqualityExpression = (Core.Name "hydra/ext/csharp/syntax.EqualityExpression")

_EqualityExpression_simple = (Core.Name "simple")

_EqualityExpression_binary = (Core.Name "binary")

data BinaryEqualityExpression = 
  BinaryEqualityExpression {
    binaryEqualityExpressionLeft :: EqualityExpression,
    binaryEqualityExpressionOperator :: EqualityOperator,
    binaryEqualityExpressionRight :: RelationalExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryEqualityExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryEqualityExpression")

_BinaryEqualityExpression_left = (Core.Name "left")

_BinaryEqualityExpression_operator = (Core.Name "operator")

_BinaryEqualityExpression_right = (Core.Name "right")

data EqualityOperator = 
  EqualityOperatorEqual  |
  EqualityOperatorNotEqual 
  deriving (Eq, Ord, Read, Show)

_EqualityOperator = (Core.Name "hydra/ext/csharp/syntax.EqualityOperator")

_EqualityOperator_equal = (Core.Name "equal")

_EqualityOperator_notEqual = (Core.Name "notEqual")

data AndExpression = 
  AndExpressionSimple EqualityExpression |
  AndExpressionBinary BinaryAndExpression
  deriving (Eq, Ord, Read, Show)

_AndExpression = (Core.Name "hydra/ext/csharp/syntax.AndExpression")

_AndExpression_simple = (Core.Name "simple")

_AndExpression_binary = (Core.Name "binary")

data BinaryAndExpression = 
  BinaryAndExpression {
    binaryAndExpressionLeft :: AndExpression,
    binaryAndExpressionRight :: EqualityExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryAndExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryAndExpression")

_BinaryAndExpression_left = (Core.Name "left")

_BinaryAndExpression_right = (Core.Name "right")

data ExclusiveOrExpression = 
  ExclusiveOrExpressionSimple AndExpression |
  ExclusiveOrExpressionBinary BinaryExclusiveOrExpression
  deriving (Eq, Ord, Read, Show)

_ExclusiveOrExpression = (Core.Name "hydra/ext/csharp/syntax.ExclusiveOrExpression")

_ExclusiveOrExpression_simple = (Core.Name "simple")

_ExclusiveOrExpression_binary = (Core.Name "binary")

data BinaryExclusiveOrExpression = 
  BinaryExclusiveOrExpression {
    binaryExclusiveOrExpressionLeft :: ExclusiveOrExpression,
    binaryExclusiveOrExpressionRight :: AndExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryExclusiveOrExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryExclusiveOrExpression")

_BinaryExclusiveOrExpression_left = (Core.Name "left")

_BinaryExclusiveOrExpression_right = (Core.Name "right")

data InclusiveOrExpression = 
  InclusiveOrExpressionSimple ExclusiveOrExpression |
  InclusiveOrExpressionBinary BinaryInclusiveOrExpression
  deriving (Eq, Ord, Read, Show)

_InclusiveOrExpression = (Core.Name "hydra/ext/csharp/syntax.InclusiveOrExpression")

_InclusiveOrExpression_simple = (Core.Name "simple")

_InclusiveOrExpression_binary = (Core.Name "binary")

data BinaryInclusiveOrExpression = 
  BinaryInclusiveOrExpression {
    binaryInclusiveOrExpressionLeft :: InclusiveOrExpression,
    binaryInclusiveOrExpressionRight :: ExclusiveOrExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryInclusiveOrExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryInclusiveOrExpression")

_BinaryInclusiveOrExpression_left = (Core.Name "left")

_BinaryInclusiveOrExpression_right = (Core.Name "right")

data ConditionalAndExpression = 
  ConditionalAndExpressionSimple InclusiveOrExpression |
  ConditionalAndExpressionBinary BinaryConditionalAndExpression
  deriving (Eq, Ord, Read, Show)

_ConditionalAndExpression = (Core.Name "hydra/ext/csharp/syntax.ConditionalAndExpression")

_ConditionalAndExpression_simple = (Core.Name "simple")

_ConditionalAndExpression_binary = (Core.Name "binary")

data BinaryConditionalAndExpression = 
  BinaryConditionalAndExpression {
    binaryConditionalAndExpressionLeft :: ConditionalAndExpression,
    binaryConditionalAndExpressionRight :: InclusiveOrExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryConditionalAndExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryConditionalAndExpression")

_BinaryConditionalAndExpression_left = (Core.Name "left")

_BinaryConditionalAndExpression_right = (Core.Name "right")

data ConditionalOrExpression = 
  ConditionalOrExpressionSimple ConditionalAndExpression |
  ConditionalOrExpressionBinary BinaryConditionalOrExpression
  deriving (Eq, Ord, Read, Show)

_ConditionalOrExpression = (Core.Name "hydra/ext/csharp/syntax.ConditionalOrExpression")

_ConditionalOrExpression_simple = (Core.Name "simple")

_ConditionalOrExpression_binary = (Core.Name "binary")

data BinaryConditionalOrExpression = 
  BinaryConditionalOrExpression {
    binaryConditionalOrExpressionLeft :: ConditionalOrExpression,
    binaryConditionalOrExpressionRight :: ConditionalAndExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryConditionalOrExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryConditionalOrExpression")

_BinaryConditionalOrExpression_left = (Core.Name "left")

_BinaryConditionalOrExpression_right = (Core.Name "right")

data NullCoalescingExpression = 
  NullCoalescingExpressionSimple ConditionalOrExpression |
  NullCoalescingExpressionBinary BinaryNullCoalescingExpression |
  NullCoalescingExpressionThrow NullCoalescingExpression
  deriving (Eq, Ord, Read, Show)

_NullCoalescingExpression = (Core.Name "hydra/ext/csharp/syntax.NullCoalescingExpression")

_NullCoalescingExpression_simple = (Core.Name "simple")

_NullCoalescingExpression_binary = (Core.Name "binary")

_NullCoalescingExpression_throw = (Core.Name "throw")

data BinaryNullCoalescingExpression = 
  BinaryNullCoalescingExpression {
    binaryNullCoalescingExpressionLeft :: ConditionalOrExpression,
    binaryNullCoalescingExpressionRight :: NullCoalescingExpression}
  deriving (Eq, Ord, Read, Show)

_BinaryNullCoalescingExpression = (Core.Name "hydra/ext/csharp/syntax.BinaryNullCoalescingExpression")

_BinaryNullCoalescingExpression_left = (Core.Name "left")

_BinaryNullCoalescingExpression_right = (Core.Name "right")

data DeclarationExpression = 
  DeclarationExpression {
    declarationExpressionType :: LocalVariableType,
    declarationExpressionIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_DeclarationExpression = (Core.Name "hydra/ext/csharp/syntax.DeclarationExpression")

_DeclarationExpression_type = (Core.Name "type")

_DeclarationExpression_identifier = (Core.Name "identifier")

data LocalVariableType = 
  LocalVariableTypeType Type |
  LocalVariableTypeVar 
  deriving (Eq, Ord, Read, Show)

_LocalVariableType = (Core.Name "hydra/ext/csharp/syntax.LocalVariableType")

_LocalVariableType_type = (Core.Name "type")

_LocalVariableType_var = (Core.Name "var")

data ConditionalExpression = 
  ConditionalExpressionSimple NullCoalescingExpression |
  ConditionalExpressionSimpleConditional SimpleConditionalExpression |
  ConditionalExpressionRefConditional RefConditionalExpression
  deriving (Eq, Ord, Read, Show)

_ConditionalExpression = (Core.Name "hydra/ext/csharp/syntax.ConditionalExpression")

_ConditionalExpression_simple = (Core.Name "simple")

_ConditionalExpression_simpleConditional = (Core.Name "simpleConditional")

_ConditionalExpression_refConditional = (Core.Name "refConditional")

data SimpleConditionalExpression = 
  SimpleConditionalExpression {
    simpleConditionalExpressionCondition :: NullCoalescingExpression,
    simpleConditionalExpressionTrue :: Expression,
    simpleConditionalExpressionFalse :: Expression}
  deriving (Eq, Ord, Read, Show)

_SimpleConditionalExpression = (Core.Name "hydra/ext/csharp/syntax.SimpleConditionalExpression")

_SimpleConditionalExpression_condition = (Core.Name "condition")

_SimpleConditionalExpression_true = (Core.Name "true")

_SimpleConditionalExpression_false = (Core.Name "false")

data RefConditionalExpression = 
  RefConditionalExpression {
    refConditionalExpressionCondition :: NullCoalescingExpression,
    refConditionalExpressionTrue :: VariableReference,
    refConditionalExpressionFalse :: VariableReference}
  deriving (Eq, Ord, Read, Show)

_RefConditionalExpression = (Core.Name "hydra/ext/csharp/syntax.RefConditionalExpression")

_RefConditionalExpression_condition = (Core.Name "condition")

_RefConditionalExpression_true = (Core.Name "true")

_RefConditionalExpression_false = (Core.Name "false")

data LambdaExpression = 
  LambdaExpression {
    lambdaExpressionAsync :: Bool,
    lambdaExpressionSignature :: AnonymousFunctionSignature,
    lambdaExpressionBody :: AnonymousFunctionBody}
  deriving (Eq, Ord, Read, Show)

_LambdaExpression = (Core.Name "hydra/ext/csharp/syntax.LambdaExpression")

_LambdaExpression_async = (Core.Name "async")

_LambdaExpression_signature = (Core.Name "signature")

_LambdaExpression_body = (Core.Name "body")

data AnonymousMethodExpression = 
  AnonymousMethodExpression {
    anonymousMethodExpressionAsync :: Bool,
    anonymousMethodExpressionSignature :: [ExplicitAnonymousFunctionParameter],
    anonymousMethodExpressionBody :: Block}
  deriving (Eq, Ord, Read, Show)

_AnonymousMethodExpression = (Core.Name "hydra/ext/csharp/syntax.AnonymousMethodExpression")

_AnonymousMethodExpression_async = (Core.Name "async")

_AnonymousMethodExpression_signature = (Core.Name "signature")

_AnonymousMethodExpression_body = (Core.Name "body")

data AnonymousFunctionSignature = 
  AnonymousFunctionSignatureExplicit [ExplicitAnonymousFunctionParameter] |
  AnonymousFunctionSignatureImplicit [Identifier]
  deriving (Eq, Ord, Read, Show)

_AnonymousFunctionSignature = (Core.Name "hydra/ext/csharp/syntax.AnonymousFunctionSignature")

_AnonymousFunctionSignature_explicit = (Core.Name "explicit")

_AnonymousFunctionSignature_implicit = (Core.Name "implicit")

data ExplicitAnonymousFunctionParameter = 
  ExplicitAnonymousFunctionParameter {
    explicitAnonymousFunctionParameterModifier :: (Maybe AnonymousFunctionParameterModifier),
    explicitAnonymousFunctionParameterType :: Type,
    explicitAnonymousFunctionParameterIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_ExplicitAnonymousFunctionParameter = (Core.Name "hydra/ext/csharp/syntax.ExplicitAnonymousFunctionParameter")

_ExplicitAnonymousFunctionParameter_modifier = (Core.Name "modifier")

_ExplicitAnonymousFunctionParameter_type = (Core.Name "type")

_ExplicitAnonymousFunctionParameter_identifier = (Core.Name "identifier")

data AnonymousFunctionParameterModifier = 
  AnonymousFunctionParameterModifierRef  |
  AnonymousFunctionParameterModifierOut  |
  AnonymousFunctionParameterModifierIn 
  deriving (Eq, Ord, Read, Show)

_AnonymousFunctionParameterModifier = (Core.Name "hydra/ext/csharp/syntax.AnonymousFunctionParameterModifier")

_AnonymousFunctionParameterModifier_ref = (Core.Name "ref")

_AnonymousFunctionParameterModifier_out = (Core.Name "out")

_AnonymousFunctionParameterModifier_in = (Core.Name "in")

data AnonymousFunctionBody = 
  AnonymousFunctionBodyNullConditionalInvocation NullConditionalInvocationExpression |
  AnonymousFunctionBodyExpression Expression |
  AnonymousFunctionBodyRef VariableReference |
  AnonymousFunctionBodyBlock Block
  deriving (Eq, Ord, Read, Show)

_AnonymousFunctionBody = (Core.Name "hydra/ext/csharp/syntax.AnonymousFunctionBody")

_AnonymousFunctionBody_nullConditionalInvocation = (Core.Name "nullConditionalInvocation")

_AnonymousFunctionBody_expression = (Core.Name "expression")

_AnonymousFunctionBody_ref = (Core.Name "ref")

_AnonymousFunctionBody_block = (Core.Name "block")

data QueryExpression = 
  QueryExpression {
    queryExpressionFrom :: FromClause,
    queryExpressionBody :: QueryBody}
  deriving (Eq, Ord, Read, Show)

_QueryExpression = (Core.Name "hydra/ext/csharp/syntax.QueryExpression")

_QueryExpression_from = (Core.Name "from")

_QueryExpression_body = (Core.Name "body")

data FromClause = 
  FromClause {
    fromClauseType :: (Maybe Type),
    fromClauseIdentifier :: Identifier,
    fromClauseIn :: Expression}
  deriving (Eq, Ord, Read, Show)

_FromClause = (Core.Name "hydra/ext/csharp/syntax.FromClause")

_FromClause_type = (Core.Name "type")

_FromClause_identifier = (Core.Name "identifier")

_FromClause_in = (Core.Name "in")

data QueryBody = 
  QueryBody {
    queryBodyClauses :: [QueryBodyClause],
    queryBodySelectOrGroup :: SelectOrGroupClause,
    queryBodyContinuation :: (Maybe QueryContinuation)}
  deriving (Eq, Ord, Read, Show)

_QueryBody = (Core.Name "hydra/ext/csharp/syntax.QueryBody")

_QueryBody_clauses = (Core.Name "clauses")

_QueryBody_selectOrGroup = (Core.Name "selectOrGroup")

_QueryBody_continuation = (Core.Name "continuation")

data QueryBodyClause = 
  QueryBodyClauseFrom FromClause |
  QueryBodyClauseLet LetClause |
  QueryBodyClauseWhere BooleanExpression |
  QueryBodyClauseJoin JoinClause |
  QueryBodyClauseOrderby [Ordering_]
  deriving (Eq, Ord, Read, Show)

_QueryBodyClause = (Core.Name "hydra/ext/csharp/syntax.QueryBodyClause")

_QueryBodyClause_from = (Core.Name "from")

_QueryBodyClause_let = (Core.Name "let")

_QueryBodyClause_where = (Core.Name "where")

_QueryBodyClause_join = (Core.Name "join")

_QueryBodyClause_orderby = (Core.Name "orderby")

data LetClause = 
  LetClause {
    letClauseLeft :: Identifier,
    letClauseRight :: Expression}
  deriving (Eq, Ord, Read, Show)

_LetClause = (Core.Name "hydra/ext/csharp/syntax.LetClause")

_LetClause_left = (Core.Name "left")

_LetClause_right = (Core.Name "right")

data JoinClause = 
  JoinClause {
    joinClauseType :: (Maybe Type),
    joinClauseIdentifier :: Identifier,
    joinClauseIn :: Expression,
    joinClauseOn :: Expression,
    joinClauseEquals :: Expression,
    joinClauseInto :: (Maybe Identifier)}
  deriving (Eq, Ord, Read, Show)

_JoinClause = (Core.Name "hydra/ext/csharp/syntax.JoinClause")

_JoinClause_type = (Core.Name "type")

_JoinClause_identifier = (Core.Name "identifier")

_JoinClause_in = (Core.Name "in")

_JoinClause_on = (Core.Name "on")

_JoinClause_equals = (Core.Name "equals")

_JoinClause_into = (Core.Name "into")

data Ordering_ = 
  Ordering_ {
    orderingExpression :: Expression,
    orderingDirection :: (Maybe OrderingDirection)}
  deriving (Eq, Ord, Read, Show)

_Ordering = (Core.Name "hydra/ext/csharp/syntax.Ordering")

_Ordering_expression = (Core.Name "expression")

_Ordering_direction = (Core.Name "direction")

data OrderingDirection = 
  OrderingDirectionAscending  |
  OrderingDirectionDescending 
  deriving (Eq, Ord, Read, Show)

_OrderingDirection = (Core.Name "hydra/ext/csharp/syntax.OrderingDirection")

_OrderingDirection_ascending = (Core.Name "ascending")

_OrderingDirection_descending = (Core.Name "descending")

data SelectOrGroupClause = 
  SelectOrGroupClauseSelect Expression |
  SelectOrGroupClauseGroup GroupClause
  deriving (Eq, Ord, Read, Show)

_SelectOrGroupClause = (Core.Name "hydra/ext/csharp/syntax.SelectOrGroupClause")

_SelectOrGroupClause_select = (Core.Name "select")

_SelectOrGroupClause_group = (Core.Name "group")

data GroupClause = 
  GroupClause {
    groupClauseGrouped :: Expression,
    groupClauseBy :: Expression}
  deriving (Eq, Ord, Read, Show)

_GroupClause = (Core.Name "hydra/ext/csharp/syntax.GroupClause")

_GroupClause_grouped = (Core.Name "grouped")

_GroupClause_by = (Core.Name "by")

data QueryContinuation = 
  QueryContinuation {
    queryContinuationInto :: Identifier,
    queryContinuationBody :: QueryBody}
  deriving (Eq, Ord, Read, Show)

_QueryContinuation = (Core.Name "hydra/ext/csharp/syntax.QueryContinuation")

_QueryContinuation_into = (Core.Name "into")

_QueryContinuation_body = (Core.Name "body")

data Assignment = 
  Assignment {
    assignmentLeft :: UnaryExpression,
    assignmentOperator :: AssignmentOperator,
    assignmentRight :: Expression}
  deriving (Eq, Ord, Read, Show)

_Assignment = (Core.Name "hydra/ext/csharp/syntax.Assignment")

_Assignment_left = (Core.Name "left")

_Assignment_operator = (Core.Name "operator")

_Assignment_right = (Core.Name "right")

data AssignmentOperator = 
  AssignmentOperatorSimple Bool |
  AssignmentOperatorPlusEquals  |
  AssignmentOperatorMinusEquals  |
  AssignmentOperatorTimesEquals  |
  AssignmentOperatorDivideEquals  |
  AssignmentOperatorModEquals  |
  AssignmentOperatorAndEquals  |
  AssignmentOperatorOrEquals  |
  AssignmentOperatorXorEquals  |
  AssignmentOperatorLeftShiftEquals  |
  AssignmentOperatorRightShiftEquals 
  deriving (Eq, Ord, Read, Show)

_AssignmentOperator = (Core.Name "hydra/ext/csharp/syntax.AssignmentOperator")

_AssignmentOperator_simple = (Core.Name "simple")

_AssignmentOperator_plusEquals = (Core.Name "plusEquals")

_AssignmentOperator_minusEquals = (Core.Name "minusEquals")

_AssignmentOperator_timesEquals = (Core.Name "timesEquals")

_AssignmentOperator_divideEquals = (Core.Name "divideEquals")

_AssignmentOperator_modEquals = (Core.Name "modEquals")

_AssignmentOperator_andEquals = (Core.Name "andEquals")

_AssignmentOperator_orEquals = (Core.Name "orEquals")

_AssignmentOperator_xorEquals = (Core.Name "xorEquals")

_AssignmentOperator_leftShiftEquals = (Core.Name "leftShiftEquals")

_AssignmentOperator_rightShiftEquals = (Core.Name "rightShiftEquals")

data Expression = 
  ExpressionNonAssignment NonAssignmentExpression |
  ExpressionAssignment Assignment
  deriving (Eq, Ord, Read, Show)

_Expression = (Core.Name "hydra/ext/csharp/syntax.Expression")

_Expression_nonAssignment = (Core.Name "nonAssignment")

_Expression_assignment = (Core.Name "assignment")

data NonAssignmentExpression = 
  NonAssignmentExpressionDeclaration DeclarationExpression |
  NonAssignmentExpressionConditional ConditionalExpression |
  NonAssignmentExpressionLambda LambdaExpression |
  NonAssignmentExpressionQuery QueryExpression
  deriving (Eq, Ord, Read, Show)

_NonAssignmentExpression = (Core.Name "hydra/ext/csharp/syntax.NonAssignmentExpression")

_NonAssignmentExpression_declaration = (Core.Name "declaration")

_NonAssignmentExpression_conditional = (Core.Name "conditional")

_NonAssignmentExpression_lambda = (Core.Name "lambda")

_NonAssignmentExpression_query = (Core.Name "query")

newtype ConstantExpression = 
  ConstantExpression {
    unConstantExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_ConstantExpression = (Core.Name "hydra/ext/csharp/syntax.ConstantExpression")

newtype BooleanExpression = 
  BooleanExpression {
    unBooleanExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_BooleanExpression = (Core.Name "hydra/ext/csharp/syntax.BooleanExpression")

data Statement = 
  StatementLabeled LabeledStatement |
  StatementDeclaration DeclarationStatement |
  StatementEmbedded EmbeddedStatement
  deriving (Eq, Ord, Read, Show)

_Statement = (Core.Name "hydra/ext/csharp/syntax.Statement")

_Statement_labeled = (Core.Name "labeled")

_Statement_declaration = (Core.Name "declaration")

_Statement_embedded = (Core.Name "embedded")

data EmbeddedStatement = 
  EmbeddedStatementBlock Block |
  EmbeddedStatementEmpty  |
  EmbeddedStatementExpression StatementExpression |
  EmbeddedStatementSelection SelectionStatement |
  EmbeddedStatementIteration IterationStatement |
  EmbeddedStatementJump JumpStatement |
  EmbeddedStatementTry TryStatement |
  EmbeddedStatementChecked Block |
  EmbeddedStatementUnchecked Block |
  EmbeddedStatementLock LockStatement |
  EmbeddedStatementUsing UsingStatement |
  EmbeddedStatementYield YieldStatement |
  EmbeddedStatementUnsafe Block |
  EmbeddedStatementFixed FixedStatement
  deriving (Eq, Ord, Read, Show)

_EmbeddedStatement = (Core.Name "hydra/ext/csharp/syntax.EmbeddedStatement")

_EmbeddedStatement_block = (Core.Name "block")

_EmbeddedStatement_empty = (Core.Name "empty")

_EmbeddedStatement_expression = (Core.Name "expression")

_EmbeddedStatement_selection = (Core.Name "selection")

_EmbeddedStatement_iteration = (Core.Name "iteration")

_EmbeddedStatement_jump = (Core.Name "jump")

_EmbeddedStatement_try = (Core.Name "try")

_EmbeddedStatement_checked = (Core.Name "checked")

_EmbeddedStatement_unchecked = (Core.Name "unchecked")

_EmbeddedStatement_lock = (Core.Name "lock")

_EmbeddedStatement_using = (Core.Name "using")

_EmbeddedStatement_yield = (Core.Name "yield")

_EmbeddedStatement_unsafe = (Core.Name "unsafe")

_EmbeddedStatement_fixed = (Core.Name "fixed")

newtype Block = 
  Block {
    unBlock :: [Statement]}
  deriving (Eq, Ord, Read, Show)

_Block = (Core.Name "hydra/ext/csharp/syntax.Block")

data LabeledStatement = 
  LabeledStatement {
    labeledStatementLabel :: Identifier,
    labeledStatementStatement :: Statement}
  deriving (Eq, Ord, Read, Show)

_LabeledStatement = (Core.Name "hydra/ext/csharp/syntax.LabeledStatement")

_LabeledStatement_label = (Core.Name "label")

_LabeledStatement_statement = (Core.Name "statement")

data DeclarationStatement = 
  DeclarationStatementVariable LocalVariableDeclaration |
  DeclarationStatementConstant LocalConstantDeclaration |
  DeclarationStatementFunction LocalFunctionDeclaration
  deriving (Eq, Ord, Read, Show)

_DeclarationStatement = (Core.Name "hydra/ext/csharp/syntax.DeclarationStatement")

_DeclarationStatement_variable = (Core.Name "variable")

_DeclarationStatement_constant = (Core.Name "constant")

_DeclarationStatement_function = (Core.Name "function")

data LocalVariableDeclaration = 
  LocalVariableDeclarationImplicitlyTyped ImplicitlyTypedLocalVariableDeclaration |
  LocalVariableDeclarationExplicitlyTyped ExplicitlyTypedLocalVariableDeclaration |
  LocalVariableDeclarationRef RefLocalVariableDeclaration
  deriving (Eq, Ord, Read, Show)

_LocalVariableDeclaration = (Core.Name "hydra/ext/csharp/syntax.LocalVariableDeclaration")

_LocalVariableDeclaration_implicitlyTyped = (Core.Name "implicitlyTyped")

_LocalVariableDeclaration_explicitlyTyped = (Core.Name "explicitlyTyped")

_LocalVariableDeclaration_ref = (Core.Name "ref")

data ImplicitlyTypedLocalVariableDeclaration = 
  ImplicitlyTypedLocalVariableDeclarationVar ImplicitlyTypedLocalVariableDeclarator |
  ImplicitlyTypedLocalVariableDeclarationRefVar RefVarImplicitlyTypedLocalVariableDeclaration
  deriving (Eq, Ord, Read, Show)

_ImplicitlyTypedLocalVariableDeclaration = (Core.Name "hydra/ext/csharp/syntax.ImplicitlyTypedLocalVariableDeclaration")

_ImplicitlyTypedLocalVariableDeclaration_var = (Core.Name "var")

_ImplicitlyTypedLocalVariableDeclaration_refVar = (Core.Name "refVar")

data RefVarImplicitlyTypedLocalVariableDeclaration = 
  RefVarImplicitlyTypedLocalVariableDeclaration {
    refVarImplicitlyTypedLocalVariableDeclarationRefKind :: RefKind,
    refVarImplicitlyTypedLocalVariableDeclarationDeclarator :: RefLocalVariableDeclarator}
  deriving (Eq, Ord, Read, Show)

_RefVarImplicitlyTypedLocalVariableDeclaration = (Core.Name "hydra/ext/csharp/syntax.RefVarImplicitlyTypedLocalVariableDeclaration")

_RefVarImplicitlyTypedLocalVariableDeclaration_refKind = (Core.Name "refKind")

_RefVarImplicitlyTypedLocalVariableDeclaration_declarator = (Core.Name "declarator")

data ImplicitlyTypedLocalVariableDeclarator = 
  ImplicitlyTypedLocalVariableDeclarator {
    implicitlyTypedLocalVariableDeclaratorIdentifier :: Identifier,
    implicitlyTypedLocalVariableDeclaratorExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_ImplicitlyTypedLocalVariableDeclarator = (Core.Name "hydra/ext/csharp/syntax.ImplicitlyTypedLocalVariableDeclarator")

_ImplicitlyTypedLocalVariableDeclarator_identifier = (Core.Name "identifier")

_ImplicitlyTypedLocalVariableDeclarator_expression = (Core.Name "expression")

data ExplicitlyTypedLocalVariableDeclaration = 
  ExplicitlyTypedLocalVariableDeclaration {
    explicitlyTypedLocalVariableDeclarationType :: Type,
    explicitlyTypedLocalVariableDeclarationDeclarators :: [ExplicitlyTypedLocalVariableDeclarator]}
  deriving (Eq, Ord, Read, Show)

_ExplicitlyTypedLocalVariableDeclaration = (Core.Name "hydra/ext/csharp/syntax.ExplicitlyTypedLocalVariableDeclaration")

_ExplicitlyTypedLocalVariableDeclaration_type = (Core.Name "type")

_ExplicitlyTypedLocalVariableDeclaration_declarators = (Core.Name "declarators")

data ExplicitlyTypedLocalVariableDeclarator = 
  ExplicitlyTypedLocalVariableDeclarator {
    explicitlyTypedLocalVariableDeclaratorIdentifier :: Identifier,
    explicitlyTypedLocalVariableDeclaratorInitializer :: (Maybe LocalVariableInitializer)}
  deriving (Eq, Ord, Read, Show)

_ExplicitlyTypedLocalVariableDeclarator = (Core.Name "hydra/ext/csharp/syntax.ExplicitlyTypedLocalVariableDeclarator")

_ExplicitlyTypedLocalVariableDeclarator_identifier = (Core.Name "identifier")

_ExplicitlyTypedLocalVariableDeclarator_initializer = (Core.Name "initializer")

data LocalVariableInitializer = 
  LocalVariableInitializerExpression Expression |
  LocalVariableInitializerInitializer ArrayInitializer
  deriving (Eq, Ord, Read, Show)

_LocalVariableInitializer = (Core.Name "hydra/ext/csharp/syntax.LocalVariableInitializer")

_LocalVariableInitializer_expression = (Core.Name "expression")

_LocalVariableInitializer_initializer = (Core.Name "initializer")

data RefLocalVariableDeclaration = 
  RefLocalVariableDeclaration {
    refLocalVariableDeclarationRefKind :: RefKind,
    refLocalVariableDeclarationType :: Type,
    refLocalVariableDeclarationDeclarators :: [RefLocalVariableDeclarator]}
  deriving (Eq, Ord, Read, Show)

_RefLocalVariableDeclaration = (Core.Name "hydra/ext/csharp/syntax.RefLocalVariableDeclaration")

_RefLocalVariableDeclaration_refKind = (Core.Name "refKind")

_RefLocalVariableDeclaration_type = (Core.Name "type")

_RefLocalVariableDeclaration_declarators = (Core.Name "declarators")

data RefLocalVariableDeclarator = 
  RefLocalVariableDeclarator {
    refLocalVariableDeclaratorLeft :: Identifier,
    refLocalVariableDeclaratorRight :: VariableReference}
  deriving (Eq, Ord, Read, Show)

_RefLocalVariableDeclarator = (Core.Name "hydra/ext/csharp/syntax.RefLocalVariableDeclarator")

_RefLocalVariableDeclarator_left = (Core.Name "left")

_RefLocalVariableDeclarator_right = (Core.Name "right")

data LocalConstantDeclaration = 
  LocalConstantDeclaration {
    localConstantDeclarationType :: Type,
    localConstantDeclarationDeclarators :: [ConstantDeclarator]}
  deriving (Eq, Ord, Read, Show)

_LocalConstantDeclaration = (Core.Name "hydra/ext/csharp/syntax.LocalConstantDeclaration")

_LocalConstantDeclaration_type = (Core.Name "type")

_LocalConstantDeclaration_declarators = (Core.Name "declarators")

data ConstantDeclarator = 
  ConstantDeclarator {
    constantDeclaratorIdentifier :: Identifier,
    constantDeclaratorExpression :: ConstantExpression}
  deriving (Eq, Ord, Read, Show)

_ConstantDeclarator = (Core.Name "hydra/ext/csharp/syntax.ConstantDeclarator")

_ConstantDeclarator_identifier = (Core.Name "identifier")

_ConstantDeclarator_expression = (Core.Name "expression")

data LocalFunctionDeclaration = 
  LocalFunctionDeclarationStandard StandardLocalFunctionDeclaration |
  LocalFunctionDeclarationRef RefLocalFunctionDeclaration
  deriving (Eq, Ord, Read, Show)

_LocalFunctionDeclaration = (Core.Name "hydra/ext/csharp/syntax.LocalFunctionDeclaration")

_LocalFunctionDeclaration_standard = (Core.Name "standard")

_LocalFunctionDeclaration_ref = (Core.Name "ref")

data StandardLocalFunctionDeclaration = 
  StandardLocalFunctionDeclaration {
    standardLocalFunctionDeclarationModifiers :: [LocalFunctionModifier],
    standardLocalFunctionDeclarationReturnType :: ReturnType,
    standardLocalFunctionDeclarationHeader :: LocalFunctionHeader,
    standardLocalFunctionDeclarationBody :: LocalFunctionBody}
  deriving (Eq, Ord, Read, Show)

_StandardLocalFunctionDeclaration = (Core.Name "hydra/ext/csharp/syntax.StandardLocalFunctionDeclaration")

_StandardLocalFunctionDeclaration_modifiers = (Core.Name "modifiers")

_StandardLocalFunctionDeclaration_returnType = (Core.Name "returnType")

_StandardLocalFunctionDeclaration_header = (Core.Name "header")

_StandardLocalFunctionDeclaration_body = (Core.Name "body")

data RefLocalFunctionDeclaration = 
  RefLocalFunctionDeclaration {
    refLocalFunctionDeclarationModifiers :: [RefLocalFunctionModifier],
    refLocalFunctionDeclarationRefKind :: RefKind,
    refLocalFunctionDeclarationReturnType :: Type,
    refLocalFunctionDeclarationHeader :: LocalFunctionHeader,
    refLocalFunctionDeclarationBody :: RefLocalFunctionBody}
  deriving (Eq, Ord, Read, Show)

_RefLocalFunctionDeclaration = (Core.Name "hydra/ext/csharp/syntax.RefLocalFunctionDeclaration")

_RefLocalFunctionDeclaration_modifiers = (Core.Name "modifiers")

_RefLocalFunctionDeclaration_refKind = (Core.Name "refKind")

_RefLocalFunctionDeclaration_returnType = (Core.Name "returnType")

_RefLocalFunctionDeclaration_header = (Core.Name "header")

_RefLocalFunctionDeclaration_body = (Core.Name "body")

data LocalFunctionHeader = 
  LocalFunctionHeader {
    localFunctionHeaderIdentifier :: Identifier,
    localFunctionHeaderTypeParameters :: (Maybe TypeParameterList),
    localFunctionHeaderParameters :: FormalParameterList,
    localFunctionHeaderConstraints :: [TypeParameterConstraintsClause]}
  deriving (Eq, Ord, Read, Show)

_LocalFunctionHeader = (Core.Name "hydra/ext/csharp/syntax.LocalFunctionHeader")

_LocalFunctionHeader_identifier = (Core.Name "identifier")

_LocalFunctionHeader_typeParameters = (Core.Name "typeParameters")

_LocalFunctionHeader_parameters = (Core.Name "parameters")

_LocalFunctionHeader_constraints = (Core.Name "constraints")

data LocalFunctionModifier = 
  LocalFunctionModifierRef RefLocalFunctionModifier |
  LocalFunctionModifierAsync 
  deriving (Eq, Ord, Read, Show)

_LocalFunctionModifier = (Core.Name "hydra/ext/csharp/syntax.LocalFunctionModifier")

_LocalFunctionModifier_ref = (Core.Name "ref")

_LocalFunctionModifier_async = (Core.Name "async")

data RefLocalFunctionModifier = 
  RefLocalFunctionModifierStatic  |
  RefLocalFunctionModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_RefLocalFunctionModifier = (Core.Name "hydra/ext/csharp/syntax.RefLocalFunctionModifier")

_RefLocalFunctionModifier_static = (Core.Name "static")

_RefLocalFunctionModifier_unsafe = (Core.Name "unsafe")

data LocalFunctionBody = 
  LocalFunctionBodyBlock Block |
  LocalFunctionBodyNullConditionalInvocation NullConditionalInvocationExpression |
  LocalFunctionBodyExpression Expression
  deriving (Eq, Ord, Read, Show)

_LocalFunctionBody = (Core.Name "hydra/ext/csharp/syntax.LocalFunctionBody")

_LocalFunctionBody_block = (Core.Name "block")

_LocalFunctionBody_nullConditionalInvocation = (Core.Name "nullConditionalInvocation")

_LocalFunctionBody_expression = (Core.Name "expression")

data RefLocalFunctionBody = 
  RefLocalFunctionBodyBlock Block |
  RefLocalFunctionBodyRef VariableReference
  deriving (Eq, Ord, Read, Show)

_RefLocalFunctionBody = (Core.Name "hydra/ext/csharp/syntax.RefLocalFunctionBody")

_RefLocalFunctionBody_block = (Core.Name "block")

_RefLocalFunctionBody_ref = (Core.Name "ref")

data StatementExpression = 
  StatementExpressionNullConditionalInvocation NullConditionalInvocationExpression |
  StatementExpressionInvocation InvocationExpression |
  StatementExpressionObjectCreation ObjectCreationExpression |
  StatementExpressionAssignment Assignment |
  StatementExpressionPostIncrement PrimaryExpression |
  StatementExpressionPostDecrement PrimaryExpression |
  StatementExpressionPreIncrement UnaryExpression |
  StatementExpressionPreDecrement UnaryExpression |
  StatementExpressionAwait UnaryExpression
  deriving (Eq, Ord, Read, Show)

_StatementExpression = (Core.Name "hydra/ext/csharp/syntax.StatementExpression")

_StatementExpression_nullConditionalInvocation = (Core.Name "nullConditionalInvocation")

_StatementExpression_invocation = (Core.Name "invocation")

_StatementExpression_objectCreation = (Core.Name "objectCreation")

_StatementExpression_assignment = (Core.Name "assignment")

_StatementExpression_postIncrement = (Core.Name "postIncrement")

_StatementExpression_postDecrement = (Core.Name "postDecrement")

_StatementExpression_preIncrement = (Core.Name "preIncrement")

_StatementExpression_preDecrement = (Core.Name "preDecrement")

_StatementExpression_await = (Core.Name "await")

data SelectionStatement = 
  SelectionStatementIf IfStatement |
  SelectionStatementSwitch SwitchStatement
  deriving (Eq, Ord, Read, Show)

_SelectionStatement = (Core.Name "hydra/ext/csharp/syntax.SelectionStatement")

_SelectionStatement_if = (Core.Name "if")

_SelectionStatement_switch = (Core.Name "switch")

data IfStatement = 
  IfStatement {
    ifStatementCondition :: BooleanExpression,
    ifStatementIfBranch :: EmbeddedStatement,
    ifStatementElseBranch :: EmbeddedStatement}
  deriving (Eq, Ord, Read, Show)

_IfStatement = (Core.Name "hydra/ext/csharp/syntax.IfStatement")

_IfStatement_condition = (Core.Name "condition")

_IfStatement_ifBranch = (Core.Name "ifBranch")

_IfStatement_elseBranch = (Core.Name "elseBranch")

data SwitchStatement = 
  SwitchStatement {
    switchStatementExpression :: Expression,
    switchStatementBranches :: [SwitchSection]}
  deriving (Eq, Ord, Read, Show)

_SwitchStatement = (Core.Name "hydra/ext/csharp/syntax.SwitchStatement")

_SwitchStatement_expression = (Core.Name "expression")

_SwitchStatement_branches = (Core.Name "branches")

data SwitchSection = 
  SwitchSection {
    switchSectionLabels :: [SwitchLabel],
    switchSectionStatements :: [Statement]}
  deriving (Eq, Ord, Read, Show)

_SwitchSection = (Core.Name "hydra/ext/csharp/syntax.SwitchSection")

_SwitchSection_labels = (Core.Name "labels")

_SwitchSection_statements = (Core.Name "statements")

data SwitchLabel = 
  SwitchLabelBranch SwitchBranch |
  SwitchLabelDefault 
  deriving (Eq, Ord, Read, Show)

_SwitchLabel = (Core.Name "hydra/ext/csharp/syntax.SwitchLabel")

_SwitchLabel_branch = (Core.Name "branch")

_SwitchLabel_default = (Core.Name "default")

data SwitchBranch = 
  SwitchBranch {
    switchBranchPattern :: Pattern,
    switchBranchGuard :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_SwitchBranch = (Core.Name "hydra/ext/csharp/syntax.SwitchBranch")

_SwitchBranch_pattern = (Core.Name "pattern")

_SwitchBranch_guard = (Core.Name "guard")

data IterationStatement = 
  IterationStatementWhile WhileStatement |
  IterationStatementDo DoStatement |
  IterationStatementFor ForStatement |
  IterationStatementForeach ForeachStatement
  deriving (Eq, Ord, Read, Show)

_IterationStatement = (Core.Name "hydra/ext/csharp/syntax.IterationStatement")

_IterationStatement_while = (Core.Name "while")

_IterationStatement_do = (Core.Name "do")

_IterationStatement_for = (Core.Name "for")

_IterationStatement_foreach = (Core.Name "foreach")

data WhileStatement = 
  WhileStatement {
    whileStatementCondition :: BooleanExpression,
    whileStatementBody :: EmbeddedStatement}
  deriving (Eq, Ord, Read, Show)

_WhileStatement = (Core.Name "hydra/ext/csharp/syntax.WhileStatement")

_WhileStatement_condition = (Core.Name "condition")

_WhileStatement_body = (Core.Name "body")

data DoStatement = 
  DoStatement {
    doStatementBody :: EmbeddedStatement,
    doStatementWhile :: BooleanExpression}
  deriving (Eq, Ord, Read, Show)

_DoStatement = (Core.Name "hydra/ext/csharp/syntax.DoStatement")

_DoStatement_body = (Core.Name "body")

_DoStatement_while = (Core.Name "while")

data ForStatement = 
  ForStatement {
    forStatementInitializer :: (Maybe ForInitializer),
    forStatementCondition :: (Maybe BooleanExpression),
    forStatementIterator :: (Maybe StatementExpressionList),
    forStatementBody :: EmbeddedStatement}
  deriving (Eq, Ord, Read, Show)

_ForStatement = (Core.Name "hydra/ext/csharp/syntax.ForStatement")

_ForStatement_initializer = (Core.Name "initializer")

_ForStatement_condition = (Core.Name "condition")

_ForStatement_iterator = (Core.Name "iterator")

_ForStatement_body = (Core.Name "body")

data ForInitializer = 
  ForInitializerVariable LocalVariableDeclaration |
  ForInitializerStatements StatementExpressionList
  deriving (Eq, Ord, Read, Show)

_ForInitializer = (Core.Name "hydra/ext/csharp/syntax.ForInitializer")

_ForInitializer_variable = (Core.Name "variable")

_ForInitializer_statements = (Core.Name "statements")

newtype StatementExpressionList = 
  StatementExpressionList {
    unStatementExpressionList :: [StatementExpression]}
  deriving (Eq, Ord, Read, Show)

_StatementExpressionList = (Core.Name "hydra/ext/csharp/syntax.StatementExpressionList")

data ForeachStatement = 
  ForeachStatement {
    foreachStatementKind :: (Maybe RefKind),
    foreachStatementType :: LocalVariableType,
    foreachStatementIdentifier :: Identifier,
    foreachStatementExpression :: Expression,
    foreachStatementBody :: EmbeddedStatement}
  deriving (Eq, Ord, Read, Show)

_ForeachStatement = (Core.Name "hydra/ext/csharp/syntax.ForeachStatement")

_ForeachStatement_kind = (Core.Name "kind")

_ForeachStatement_type = (Core.Name "type")

_ForeachStatement_identifier = (Core.Name "identifier")

_ForeachStatement_expression = (Core.Name "expression")

_ForeachStatement_body = (Core.Name "body")

data JumpStatement = 
  JumpStatementBreak  |
  JumpStatementContinue  |
  JumpStatementGoto GotoStatement |
  JumpStatementReturn ReturnStatement |
  JumpStatementThrow (Maybe Expression)
  deriving (Eq, Ord, Read, Show)

_JumpStatement = (Core.Name "hydra/ext/csharp/syntax.JumpStatement")

_JumpStatement_break = (Core.Name "break")

_JumpStatement_continue = (Core.Name "continue")

_JumpStatement_goto = (Core.Name "goto")

_JumpStatement_return = (Core.Name "return")

_JumpStatement_throw = (Core.Name "throw")

data GotoStatement = 
  GotoStatementIdentifier Identifier |
  GotoStatementCase ConstantExpression |
  GotoStatementDefault 
  deriving (Eq, Ord, Read, Show)

_GotoStatement = (Core.Name "hydra/ext/csharp/syntax.GotoStatement")

_GotoStatement_identifier = (Core.Name "identifier")

_GotoStatement_case = (Core.Name "case")

_GotoStatement_default = (Core.Name "default")

data ReturnStatement = 
  ReturnStatementSimple  |
  ReturnStatementValue Expression |
  ReturnStatementRef VariableReference
  deriving (Eq, Ord, Read, Show)

_ReturnStatement = (Core.Name "hydra/ext/csharp/syntax.ReturnStatement")

_ReturnStatement_simple = (Core.Name "simple")

_ReturnStatement_value = (Core.Name "value")

_ReturnStatement_ref = (Core.Name "ref")

data TryStatement = 
  TryStatement {
    tryStatementBody :: Block,
    tryStatementCatches :: CatchClauses,
    tryStatementFinally :: (Maybe Block)}
  deriving (Eq, Ord, Read, Show)

_TryStatement = (Core.Name "hydra/ext/csharp/syntax.TryStatement")

_TryStatement_body = (Core.Name "body")

_TryStatement_catches = (Core.Name "catches")

_TryStatement_finally = (Core.Name "finally")

data CatchClauses = 
  CatchClausesSpecific [SpecificCatchClause] |
  CatchClausesGeneral Block
  deriving (Eq, Ord, Read, Show)

_CatchClauses = (Core.Name "hydra/ext/csharp/syntax.CatchClauses")

_CatchClauses_specific = (Core.Name "specific")

_CatchClauses_general = (Core.Name "general")

data SpecificCatchClause = 
  SpecificCatchClause {
    specificCatchClauseSpecifier :: (Maybe ExceptionSpecifier),
    specificCatchClauseFilter :: (Maybe BooleanExpression),
    specificCatchClauseBody :: Block}
  deriving (Eq, Ord, Read, Show)

_SpecificCatchClause = (Core.Name "hydra/ext/csharp/syntax.SpecificCatchClause")

_SpecificCatchClause_specifier = (Core.Name "specifier")

_SpecificCatchClause_filter = (Core.Name "filter")

_SpecificCatchClause_body = (Core.Name "body")

data ExceptionSpecifier = 
  ExceptionSpecifier {
    exceptionSpecifierType :: Type,
    exceptionSpecifierIdentifier :: (Maybe Identifier)}
  deriving (Eq, Ord, Read, Show)

_ExceptionSpecifier = (Core.Name "hydra/ext/csharp/syntax.ExceptionSpecifier")

_ExceptionSpecifier_type = (Core.Name "type")

_ExceptionSpecifier_identifier = (Core.Name "identifier")

data LockStatement = 
  LockStatement {
    lockStatementExpression :: Expression,
    lockStatementBody :: EmbeddedStatement}
  deriving (Eq, Ord, Read, Show)

_LockStatement = (Core.Name "hydra/ext/csharp/syntax.LockStatement")

_LockStatement_expression = (Core.Name "expression")

_LockStatement_body = (Core.Name "body")

data UsingStatement = 
  UsingStatement {
    usingStatementAcquisition :: ResourceAcquisition,
    usingStatementBody :: EmbeddedStatement}
  deriving (Eq, Ord, Read, Show)

_UsingStatement = (Core.Name "hydra/ext/csharp/syntax.UsingStatement")

_UsingStatement_acquisition = (Core.Name "acquisition")

_UsingStatement_body = (Core.Name "body")

data ResourceAcquisition = 
  ResourceAcquisitionLocal LocalVariableDeclaration |
  ResourceAcquisitionExpression Expression
  deriving (Eq, Ord, Read, Show)

_ResourceAcquisition = (Core.Name "hydra/ext/csharp/syntax.ResourceAcquisition")

_ResourceAcquisition_local = (Core.Name "local")

_ResourceAcquisition_expression = (Core.Name "expression")

data YieldStatement = 
  YieldStatementReturn Expression |
  YieldStatementBreak 
  deriving (Eq, Ord, Read, Show)

_YieldStatement = (Core.Name "hydra/ext/csharp/syntax.YieldStatement")

_YieldStatement_return = (Core.Name "return")

_YieldStatement_break = (Core.Name "break")

data CompilationUnit = 
  CompilationUnit {
    compilationUnitExterns :: [ExternAliasDirective],
    compilationUnitUsings :: [UsingDirective],
    compilationUnitAttributes :: [GlobalAttributeSection],
    compilationUnitMembers :: [NamespaceMemberDeclaration]}
  deriving (Eq, Ord, Read, Show)

_CompilationUnit = (Core.Name "hydra/ext/csharp/syntax.CompilationUnit")

_CompilationUnit_externs = (Core.Name "externs")

_CompilationUnit_usings = (Core.Name "usings")

_CompilationUnit_attributes = (Core.Name "attributes")

_CompilationUnit_members = (Core.Name "members")

data NamespaceDeclaration = 
  NamespaceDeclaration {
    namespaceDeclarationName :: QualifiedIdentifier,
    namespaceDeclarationBody :: NamespaceBody}
  deriving (Eq, Ord, Read, Show)

_NamespaceDeclaration = (Core.Name "hydra/ext/csharp/syntax.NamespaceDeclaration")

_NamespaceDeclaration_name = (Core.Name "name")

_NamespaceDeclaration_body = (Core.Name "body")

newtype QualifiedIdentifier = 
  QualifiedIdentifier {
    unQualifiedIdentifier :: [Identifier]}
  deriving (Eq, Ord, Read, Show)

_QualifiedIdentifier = (Core.Name "hydra/ext/csharp/syntax.QualifiedIdentifier")

data NamespaceBody = 
  NamespaceBody {
    namespaceBodyExterns :: [ExternAliasDirective],
    namespaceBodyUsings :: [UsingDirective],
    namespaceBodyMembers :: [NamespaceMemberDeclaration]}
  deriving (Eq, Ord, Read, Show)

_NamespaceBody = (Core.Name "hydra/ext/csharp/syntax.NamespaceBody")

_NamespaceBody_externs = (Core.Name "externs")

_NamespaceBody_usings = (Core.Name "usings")

_NamespaceBody_members = (Core.Name "members")

newtype ExternAliasDirective = 
  ExternAliasDirective {
    unExternAliasDirective :: Identifier}
  deriving (Eq, Ord, Read, Show)

_ExternAliasDirective = (Core.Name "hydra/ext/csharp/syntax.ExternAliasDirective")

data UsingDirective = 
  UsingDirectiveAlias UsingAliasDirective |
  UsingDirectiveNamespace NamespaceName |
  UsingDirectiveStatic TypeName
  deriving (Eq, Ord, Read, Show)

_UsingDirective = (Core.Name "hydra/ext/csharp/syntax.UsingDirective")

_UsingDirective_alias = (Core.Name "alias")

_UsingDirective_namespace = (Core.Name "namespace")

_UsingDirective_static = (Core.Name "static")

data UsingAliasDirective = 
  UsingAliasDirective {
    usingAliasDirectiveAlias :: Identifier,
    usingAliasDirectiveName :: NamespaceOrTypeName}
  deriving (Eq, Ord, Read, Show)

_UsingAliasDirective = (Core.Name "hydra/ext/csharp/syntax.UsingAliasDirective")

_UsingAliasDirective_alias = (Core.Name "alias")

_UsingAliasDirective_name = (Core.Name "name")

data NamespaceMemberDeclaration = 
  NamespaceMemberDeclarationNamespace NamespaceDeclaration |
  NamespaceMemberDeclarationType TypeDeclaration
  deriving (Eq, Ord, Read, Show)

_NamespaceMemberDeclaration = (Core.Name "hydra/ext/csharp/syntax.NamespaceMemberDeclaration")

_NamespaceMemberDeclaration_namespace = (Core.Name "namespace")

_NamespaceMemberDeclaration_type = (Core.Name "type")

data TypeDeclaration = 
  TypeDeclarationClass ClassDeclaration |
  TypeDeclarationStruct StructDeclaration |
  TypeDeclarationInterface InterfaceDeclaration |
  TypeDeclarationEnum EnumDeclaration |
  TypeDeclarationDelegate DelegateDeclaration
  deriving (Eq, Ord, Read, Show)

_TypeDeclaration = (Core.Name "hydra/ext/csharp/syntax.TypeDeclaration")

_TypeDeclaration_class = (Core.Name "class")

_TypeDeclaration_struct = (Core.Name "struct")

_TypeDeclaration_interface = (Core.Name "interface")

_TypeDeclaration_enum = (Core.Name "enum")

_TypeDeclaration_delegate = (Core.Name "delegate")

data QualifiedAliasMember = 
  QualifiedAliasMember {
    qualifiedAliasMemberAlias :: Identifier,
    qualifiedAliasMemberMember :: Identifier,
    qualifiedAliasMemberArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_QualifiedAliasMember = (Core.Name "hydra/ext/csharp/syntax.QualifiedAliasMember")

_QualifiedAliasMember_alias = (Core.Name "alias")

_QualifiedAliasMember_member = (Core.Name "member")

_QualifiedAliasMember_arguments = (Core.Name "arguments")

data ClassDeclaration = 
  ClassDeclaration {
    classDeclarationAttributes :: [AttributeSection],
    classDeclarationModifiers :: [ClassModifier],
    classDeclarationPartial :: Bool,
    classDeclarationName :: Identifier,
    classDeclarationParameters :: (Maybe TypeParameterList),
    classDeclarationBase :: (Maybe ClassBase),
    classDeclarationConstraints :: [TypeParameterConstraintsClause],
    classDeclarationBody :: ClassBody}
  deriving (Eq, Ord, Read, Show)

_ClassDeclaration = (Core.Name "hydra/ext/csharp/syntax.ClassDeclaration")

_ClassDeclaration_attributes = (Core.Name "attributes")

_ClassDeclaration_modifiers = (Core.Name "modifiers")

_ClassDeclaration_partial = (Core.Name "partial")

_ClassDeclaration_name = (Core.Name "name")

_ClassDeclaration_parameters = (Core.Name "parameters")

_ClassDeclaration_base = (Core.Name "base")

_ClassDeclaration_constraints = (Core.Name "constraints")

_ClassDeclaration_body = (Core.Name "body")

data ClassModifier = 
  ClassModifierNew  |
  ClassModifierPublic  |
  ClassModifierProtected  |
  ClassModifierInternal  |
  ClassModifierPrivate  |
  ClassModifierAbstract  |
  ClassModifierSealed  |
  ClassModifierStatic  |
  ClassModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_ClassModifier = (Core.Name "hydra/ext/csharp/syntax.ClassModifier")

_ClassModifier_new = (Core.Name "new")

_ClassModifier_public = (Core.Name "public")

_ClassModifier_protected = (Core.Name "protected")

_ClassModifier_internal = (Core.Name "internal")

_ClassModifier_private = (Core.Name "private")

_ClassModifier_abstract = (Core.Name "abstract")

_ClassModifier_sealed = (Core.Name "sealed")

_ClassModifier_static = (Core.Name "static")

_ClassModifier_unsafe = (Core.Name "unsafe")

newtype TypeParameterList = 
  TypeParameterList {
    unTypeParameterList :: [TypeParameterPart]}
  deriving (Eq, Ord, Read, Show)

_TypeParameterList = (Core.Name "hydra/ext/csharp/syntax.TypeParameterList")

data TypeParameterPart = 
  TypeParameterPart {
    typeParameterPartAttributes :: (Maybe Attributes),
    typeParameterPartName :: TypeParameter}
  deriving (Eq, Ord, Read, Show)

_TypeParameterPart = (Core.Name "hydra/ext/csharp/syntax.TypeParameterPart")

_TypeParameterPart_attributes = (Core.Name "attributes")

_TypeParameterPart_name = (Core.Name "name")

data ClassBase = 
  ClassBaseClass (Maybe ClassType) |
  ClassBaseInterfaces [InterfaceType]
  deriving (Eq, Ord, Read, Show)

_ClassBase = (Core.Name "hydra/ext/csharp/syntax.ClassBase")

_ClassBase_class = (Core.Name "class")

_ClassBase_interfaces = (Core.Name "interfaces")

data TypeParameterConstraintsClause = 
  TypeParameterConstraintsClause {
    typeParameterConstraintsClauseParameter :: TypeParameter,
    typeParameterConstraintsClauseConstraints :: [TypeParameterConstraints]}
  deriving (Eq, Ord, Read, Show)

_TypeParameterConstraintsClause = (Core.Name "hydra/ext/csharp/syntax.TypeParameterConstraintsClause")

_TypeParameterConstraintsClause_parameter = (Core.Name "parameter")

_TypeParameterConstraintsClause_constraints = (Core.Name "constraints")

data TypeParameterConstraints = 
  TypeParameterConstraints {
    typeParameterConstraintsPrimary :: (Maybe PrimaryConstraint),
    typeParameterConstraintsSecondary :: (Maybe SecondaryConstraints),
    typeParameterConstraintsConstructor :: Bool}
  deriving (Eq, Ord, Read, Show)

_TypeParameterConstraints = (Core.Name "hydra/ext/csharp/syntax.TypeParameterConstraints")

_TypeParameterConstraints_primary = (Core.Name "primary")

_TypeParameterConstraints_secondary = (Core.Name "secondary")

_TypeParameterConstraints_constructor = (Core.Name "constructor")

data PrimaryConstraint = 
  PrimaryConstraintClassType ClassType |
  PrimaryConstraintClass  |
  PrimaryConstraintStruct  |
  PrimaryConstraintUnmanaged 
  deriving (Eq, Ord, Read, Show)

_PrimaryConstraint = (Core.Name "hydra/ext/csharp/syntax.PrimaryConstraint")

_PrimaryConstraint_classType = (Core.Name "classType")

_PrimaryConstraint_class = (Core.Name "class")

_PrimaryConstraint_struct = (Core.Name "struct")

_PrimaryConstraint_unmanaged = (Core.Name "unmanaged")

newtype SecondaryConstraints = 
  SecondaryConstraints {
    unSecondaryConstraints :: [SecondaryConstraint]}
  deriving (Eq, Ord, Read, Show)

_SecondaryConstraints = (Core.Name "hydra/ext/csharp/syntax.SecondaryConstraints")

data SecondaryConstraint = 
  SecondaryConstraintInterface InterfaceType |
  SecondaryConstraintParameter TypeParameter
  deriving (Eq, Ord, Read, Show)

_SecondaryConstraint = (Core.Name "hydra/ext/csharp/syntax.SecondaryConstraint")

_SecondaryConstraint_interface = (Core.Name "interface")

_SecondaryConstraint_parameter = (Core.Name "parameter")

newtype ClassBody = 
  ClassBody {
    unClassBody :: [ClassMemberDeclaration]}
  deriving (Eq, Ord, Read, Show)

_ClassBody = (Core.Name "hydra/ext/csharp/syntax.ClassBody")

data ClassMemberDeclaration = 
  ClassMemberDeclarationConstant ConstantDeclaration |
  ClassMemberDeclarationField FieldDeclaration |
  ClassMemberDeclarationMethod MethodDeclaration |
  ClassMemberDeclarationProperty PropertyDeclaration |
  ClassMemberDeclarationEvent EventDeclaration |
  ClassMemberDeclarationIndexer IndexerDeclaration |
  ClassMemberDeclarationOperator OperatorDeclaration |
  ClassMemberDeclarationConstructor ConstructorDeclaration |
  ClassMemberDeclarationFinalizer FinalizerDeclaration |
  ClassMemberDeclarationStaticConstructor StaticConstructorDeclaration |
  ClassMemberDeclarationType TypeDeclaration
  deriving (Eq, Ord, Read, Show)

_ClassMemberDeclaration = (Core.Name "hydra/ext/csharp/syntax.ClassMemberDeclaration")

_ClassMemberDeclaration_constant = (Core.Name "constant")

_ClassMemberDeclaration_field = (Core.Name "field")

_ClassMemberDeclaration_method = (Core.Name "method")

_ClassMemberDeclaration_property = (Core.Name "property")

_ClassMemberDeclaration_event = (Core.Name "event")

_ClassMemberDeclaration_indexer = (Core.Name "indexer")

_ClassMemberDeclaration_operator = (Core.Name "operator")

_ClassMemberDeclaration_constructor = (Core.Name "constructor")

_ClassMemberDeclaration_finalizer = (Core.Name "finalizer")

_ClassMemberDeclaration_staticConstructor = (Core.Name "staticConstructor")

_ClassMemberDeclaration_type = (Core.Name "type")

data ConstantDeclaration = 
  ConstantDeclaration {
    constantDeclarationAttributes :: (Maybe Attributes),
    constantDeclarationModifiers :: [ConstantModifier],
    constantDeclarationType :: Type,
    constantDeclarationDeclarators :: [ConstantDeclarator]}
  deriving (Eq, Ord, Read, Show)

_ConstantDeclaration = (Core.Name "hydra/ext/csharp/syntax.ConstantDeclaration")

_ConstantDeclaration_attributes = (Core.Name "attributes")

_ConstantDeclaration_modifiers = (Core.Name "modifiers")

_ConstantDeclaration_type = (Core.Name "type")

_ConstantDeclaration_declarators = (Core.Name "declarators")

data ConstantModifier = 
  ConstantModifierNew  |
  ConstantModifierPublic  |
  ConstantModifierProtected  |
  ConstantModifierInternal  |
  ConstantModifierPrivate 
  deriving (Eq, Ord, Read, Show)

_ConstantModifier = (Core.Name "hydra/ext/csharp/syntax.ConstantModifier")

_ConstantModifier_new = (Core.Name "new")

_ConstantModifier_public = (Core.Name "public")

_ConstantModifier_protected = (Core.Name "protected")

_ConstantModifier_internal = (Core.Name "internal")

_ConstantModifier_private = (Core.Name "private")

data FieldDeclaration = 
  FieldDeclaration {
    fieldDeclarationAttributes :: (Maybe Attributes),
    fieldDeclarationModifiers :: [FieldModifier],
    fieldDeclarationType :: Type,
    fieldDeclarationDeclarators :: [VariableDeclarator]}
  deriving (Eq, Ord, Read, Show)

_FieldDeclaration = (Core.Name "hydra/ext/csharp/syntax.FieldDeclaration")

_FieldDeclaration_attributes = (Core.Name "attributes")

_FieldDeclaration_modifiers = (Core.Name "modifiers")

_FieldDeclaration_type = (Core.Name "type")

_FieldDeclaration_declarators = (Core.Name "declarators")

data FieldModifier = 
  FieldModifierNew  |
  FieldModifierPublic  |
  FieldModifierProtected  |
  FieldModifierInternal  |
  FieldModifierPrivate  |
  FieldModifierStatic  |
  FieldModifierReadonly  |
  FieldModifierVolatile  |
  FieldModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_FieldModifier = (Core.Name "hydra/ext/csharp/syntax.FieldModifier")

_FieldModifier_new = (Core.Name "new")

_FieldModifier_public = (Core.Name "public")

_FieldModifier_protected = (Core.Name "protected")

_FieldModifier_internal = (Core.Name "internal")

_FieldModifier_private = (Core.Name "private")

_FieldModifier_static = (Core.Name "static")

_FieldModifier_readonly = (Core.Name "readonly")

_FieldModifier_volatile = (Core.Name "volatile")

_FieldModifier_unsafe = (Core.Name "unsafe")

newtype VariableDeclarators = 
  VariableDeclarators {
    unVariableDeclarators :: [VariableDeclarator]}
  deriving (Eq, Ord, Read, Show)

_VariableDeclarators = (Core.Name "hydra/ext/csharp/syntax.VariableDeclarators")

data VariableDeclarator = 
  VariableDeclarator {
    variableDeclaratorIdentifier :: Identifier,
    variableDeclaratorInitializer :: (Maybe VariableInitializer)}
  deriving (Eq, Ord, Read, Show)

_VariableDeclarator = (Core.Name "hydra/ext/csharp/syntax.VariableDeclarator")

_VariableDeclarator_identifier = (Core.Name "identifier")

_VariableDeclarator_initializer = (Core.Name "initializer")

data MethodDeclaration = 
  MethodDeclarationStandard StandardMethodDeclaration |
  MethodDeclarationRefReturn RefReturnMethodDeclaration
  deriving (Eq, Ord, Read, Show)

_MethodDeclaration = (Core.Name "hydra/ext/csharp/syntax.MethodDeclaration")

_MethodDeclaration_standard = (Core.Name "standard")

_MethodDeclaration_refReturn = (Core.Name "refReturn")

data StandardMethodDeclaration = 
  StandardMethodDeclaration {
    standardMethodDeclarationAttributes :: (Maybe Attributes),
    standardMethodDeclarationModifiers :: [MethodModifier],
    standardMethodDeclarationReturnType :: ReturnType,
    standardMethodDeclarationHeader :: MethodHeader,
    standardMethodDeclarationBody :: MethodBody}
  deriving (Eq, Ord, Read, Show)

_StandardMethodDeclaration = (Core.Name "hydra/ext/csharp/syntax.StandardMethodDeclaration")

_StandardMethodDeclaration_attributes = (Core.Name "attributes")

_StandardMethodDeclaration_modifiers = (Core.Name "modifiers")

_StandardMethodDeclaration_returnType = (Core.Name "returnType")

_StandardMethodDeclaration_header = (Core.Name "header")

_StandardMethodDeclaration_body = (Core.Name "body")

data RefReturnMethodDeclaration = 
  RefReturnMethodDeclaration {
    refReturnMethodDeclarationAttributes :: (Maybe Attributes),
    refReturnMethodDeclarationModifiers :: [RefMethodModifier],
    refReturnMethodDeclarationKind :: RefKind,
    refReturnMethodDeclarationReturnType :: ReturnType,
    refReturnMethodDeclarationHeader :: MethodHeader,
    refReturnMethodDeclarationBody :: RefMethodBody}
  deriving (Eq, Ord, Read, Show)

_RefReturnMethodDeclaration = (Core.Name "hydra/ext/csharp/syntax.RefReturnMethodDeclaration")

_RefReturnMethodDeclaration_attributes = (Core.Name "attributes")

_RefReturnMethodDeclaration_modifiers = (Core.Name "modifiers")

_RefReturnMethodDeclaration_kind = (Core.Name "kind")

_RefReturnMethodDeclaration_returnType = (Core.Name "returnType")

_RefReturnMethodDeclaration_header = (Core.Name "header")

_RefReturnMethodDeclaration_body = (Core.Name "body")

data MethodModifiers = 
  MethodModifiers {
    methodModifiersModifiers :: [MethodModifier],
    methodModifiersPartial :: Bool}
  deriving (Eq, Ord, Read, Show)

_MethodModifiers = (Core.Name "hydra/ext/csharp/syntax.MethodModifiers")

_MethodModifiers_modifiers = (Core.Name "modifiers")

_MethodModifiers_partial = (Core.Name "partial")

data RefKind = 
  RefKindRef  |
  RefKindRefReadonly 
  deriving (Eq, Ord, Read, Show)

_RefKind = (Core.Name "hydra/ext/csharp/syntax.RefKind")

_RefKind_ref = (Core.Name "ref")

_RefKind_refReadonly = (Core.Name "refReadonly")

data MethodHeader = 
  MethodHeader {
    methodHeaderName :: MemberName,
    methodHeaderTypeParameters :: (Maybe TypeParameterList),
    methodHeaderParameters :: (Maybe FormalParameterList),
    methodHeaderConstraints :: [TypeParameterConstraintsClause]}
  deriving (Eq, Ord, Read, Show)

_MethodHeader = (Core.Name "hydra/ext/csharp/syntax.MethodHeader")

_MethodHeader_name = (Core.Name "name")

_MethodHeader_typeParameters = (Core.Name "typeParameters")

_MethodHeader_parameters = (Core.Name "parameters")

_MethodHeader_constraints = (Core.Name "constraints")

data MethodModifier = 
  MethodModifierRef RefMethodModifier |
  MethodModifierAsync 
  deriving (Eq, Ord, Read, Show)

_MethodModifier = (Core.Name "hydra/ext/csharp/syntax.MethodModifier")

_MethodModifier_ref = (Core.Name "ref")

_MethodModifier_async = (Core.Name "async")

data RefMethodModifier = 
  RefMethodModifierNew  |
  RefMethodModifierPublic  |
  RefMethodModifierProtected  |
  RefMethodModifierInternal  |
  RefMethodModifierPrivate  |
  RefMethodModifierStatic  |
  RefMethodModifierVirtual  |
  RefMethodModifierSealed  |
  RefMethodModifierOverride  |
  RefMethodModifierAbstract  |
  RefMethodModifierExtern  |
  RefMethodModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_RefMethodModifier = (Core.Name "hydra/ext/csharp/syntax.RefMethodModifier")

_RefMethodModifier_new = (Core.Name "new")

_RefMethodModifier_public = (Core.Name "public")

_RefMethodModifier_protected = (Core.Name "protected")

_RefMethodModifier_internal = (Core.Name "internal")

_RefMethodModifier_private = (Core.Name "private")

_RefMethodModifier_static = (Core.Name "static")

_RefMethodModifier_virtual = (Core.Name "virtual")

_RefMethodModifier_sealed = (Core.Name "sealed")

_RefMethodModifier_override = (Core.Name "override")

_RefMethodModifier_abstract = (Core.Name "abstract")

_RefMethodModifier_extern = (Core.Name "extern")

_RefMethodModifier_unsafe = (Core.Name "unsafe")

data ReturnType = 
  ReturnTypeRef Type |
  ReturnTypeVoid 
  deriving (Eq, Ord, Read, Show)

_ReturnType = (Core.Name "hydra/ext/csharp/syntax.ReturnType")

_ReturnType_ref = (Core.Name "ref")

_ReturnType_void = (Core.Name "void")

data MemberName = 
  MemberName {
    memberNameInterfaceType :: (Maybe TypeName),
    memberNameIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_MemberName = (Core.Name "hydra/ext/csharp/syntax.MemberName")

_MemberName_interfaceType = (Core.Name "interfaceType")

_MemberName_identifier = (Core.Name "identifier")

data MethodBody = 
  MethodBodyBlock Block |
  MethodBodyNullConditionalInvocation NullConditionalInvocationExpression |
  MethodBodyExpression Expression |
  MethodBodyEmpty 
  deriving (Eq, Ord, Read, Show)

_MethodBody = (Core.Name "hydra/ext/csharp/syntax.MethodBody")

_MethodBody_block = (Core.Name "block")

_MethodBody_nullConditionalInvocation = (Core.Name "nullConditionalInvocation")

_MethodBody_expression = (Core.Name "expression")

_MethodBody_empty = (Core.Name "empty")

data RefMethodBody = 
  RefMethodBodyBlock Block |
  RefMethodBodyRef VariableReference |
  RefMethodBodyEmpty 
  deriving (Eq, Ord, Read, Show)

_RefMethodBody = (Core.Name "hydra/ext/csharp/syntax.RefMethodBody")

_RefMethodBody_block = (Core.Name "block")

_RefMethodBody_ref = (Core.Name "ref")

_RefMethodBody_empty = (Core.Name "empty")

data FormalParameterList = 
  FormalParameterList {
    formalParameterListFixed :: [FixedParameter],
    formalParameterListArray :: (Maybe ParameterArray)}
  deriving (Eq, Ord, Read, Show)

_FormalParameterList = (Core.Name "hydra/ext/csharp/syntax.FormalParameterList")

_FormalParameterList_fixed = (Core.Name "fixed")

_FormalParameterList_array = (Core.Name "array")

data FixedParameter = 
  FixedParameter {
    fixedParameterAttributes :: (Maybe Attributes),
    fixedParameterModifier :: (Maybe ParameterModifier),
    fixedParameterType :: Type,
    fixedParameterIdentifier :: Identifier,
    fixedParameterDefaultArgument :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_FixedParameter = (Core.Name "hydra/ext/csharp/syntax.FixedParameter")

_FixedParameter_attributes = (Core.Name "attributes")

_FixedParameter_modifier = (Core.Name "modifier")

_FixedParameter_type = (Core.Name "type")

_FixedParameter_identifier = (Core.Name "identifier")

_FixedParameter_defaultArgument = (Core.Name "defaultArgument")

data ParameterModifier = 
  ParameterModifierMode ParameterModeModifier |
  ParameterModifierThis 
  deriving (Eq, Ord, Read, Show)

_ParameterModifier = (Core.Name "hydra/ext/csharp/syntax.ParameterModifier")

_ParameterModifier_mode = (Core.Name "mode")

_ParameterModifier_this = (Core.Name "this")

data ParameterModeModifier = 
  ParameterModeModifierRef  |
  ParameterModeModifierOut  |
  ParameterModeModifierIn 
  deriving (Eq, Ord, Read, Show)

_ParameterModeModifier = (Core.Name "hydra/ext/csharp/syntax.ParameterModeModifier")

_ParameterModeModifier_ref = (Core.Name "ref")

_ParameterModeModifier_out = (Core.Name "out")

_ParameterModeModifier_in = (Core.Name "in")

data ParameterArray = 
  ParameterArray {
    parameterArrayAttributes :: (Maybe Attributes),
    parameterArrayType :: ArrayType,
    parameterArrayIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_ParameterArray = (Core.Name "hydra/ext/csharp/syntax.ParameterArray")

_ParameterArray_attributes = (Core.Name "attributes")

_ParameterArray_type = (Core.Name "type")

_ParameterArray_identifier = (Core.Name "identifier")

data PropertyDeclaration = 
  PropertyDeclarationStandard StandardPropertyDeclaration |
  PropertyDeclarationRefReturn RefReturnPropertyDeclaration
  deriving (Eq, Ord, Read, Show)

_PropertyDeclaration = (Core.Name "hydra/ext/csharp/syntax.PropertyDeclaration")

_PropertyDeclaration_standard = (Core.Name "standard")

_PropertyDeclaration_refReturn = (Core.Name "refReturn")

data StandardPropertyDeclaration = 
  StandardPropertyDeclaration {
    standardPropertyDeclarationAttributes :: (Maybe Attributes),
    standardPropertyDeclarationModifiers :: [PropertyModifier],
    standardPropertyDeclarationType :: Type,
    standardPropertyDeclarationName :: MemberName,
    standardPropertyDeclarationBody :: PropertyBody}
  deriving (Eq, Ord, Read, Show)

_StandardPropertyDeclaration = (Core.Name "hydra/ext/csharp/syntax.StandardPropertyDeclaration")

_StandardPropertyDeclaration_attributes = (Core.Name "attributes")

_StandardPropertyDeclaration_modifiers = (Core.Name "modifiers")

_StandardPropertyDeclaration_type = (Core.Name "type")

_StandardPropertyDeclaration_name = (Core.Name "name")

_StandardPropertyDeclaration_body = (Core.Name "body")

data RefReturnPropertyDeclaration = 
  RefReturnPropertyDeclaration {
    refReturnPropertyDeclarationAttributes :: (Maybe Attributes),
    refReturnPropertyDeclarationModifiers :: [PropertyModifier],
    refReturnPropertyDeclarationRefKind :: RefKind,
    refReturnPropertyDeclarationType :: Type,
    refReturnPropertyDeclarationName :: MemberName,
    refReturnPropertyDeclarationBody :: RefPropertyBody}
  deriving (Eq, Ord, Read, Show)

_RefReturnPropertyDeclaration = (Core.Name "hydra/ext/csharp/syntax.RefReturnPropertyDeclaration")

_RefReturnPropertyDeclaration_attributes = (Core.Name "attributes")

_RefReturnPropertyDeclaration_modifiers = (Core.Name "modifiers")

_RefReturnPropertyDeclaration_refKind = (Core.Name "refKind")

_RefReturnPropertyDeclaration_type = (Core.Name "type")

_RefReturnPropertyDeclaration_name = (Core.Name "name")

_RefReturnPropertyDeclaration_body = (Core.Name "body")

data PropertyModifier = 
  PropertyModifierNew  |
  PropertyModifierPublic  |
  PropertyModifierProtected  |
  PropertyModifierInternal  |
  PropertyModifierPrivate  |
  PropertyModifierStatic  |
  PropertyModifierVirtual  |
  PropertyModifierSealed  |
  PropertyModifierOverride  |
  PropertyModifierAbstract  |
  PropertyModifierExtern  |
  PropertyModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_PropertyModifier = (Core.Name "hydra/ext/csharp/syntax.PropertyModifier")

_PropertyModifier_new = (Core.Name "new")

_PropertyModifier_public = (Core.Name "public")

_PropertyModifier_protected = (Core.Name "protected")

_PropertyModifier_internal = (Core.Name "internal")

_PropertyModifier_private = (Core.Name "private")

_PropertyModifier_static = (Core.Name "static")

_PropertyModifier_virtual = (Core.Name "virtual")

_PropertyModifier_sealed = (Core.Name "sealed")

_PropertyModifier_override = (Core.Name "override")

_PropertyModifier_abstract = (Core.Name "abstract")

_PropertyModifier_extern = (Core.Name "extern")

_PropertyModifier_unsafe = (Core.Name "unsafe")

data PropertyBody = 
  PropertyBodyBlock BlockPropertyBody |
  PropertyBodyExpression Expression
  deriving (Eq, Ord, Read, Show)

_PropertyBody = (Core.Name "hydra/ext/csharp/syntax.PropertyBody")

_PropertyBody_block = (Core.Name "block")

_PropertyBody_expression = (Core.Name "expression")

data BlockPropertyBody = 
  BlockPropertyBody {
    blockPropertyBodyAccessors :: AccessorDeclarations,
    blockPropertyBodyInitializer :: (Maybe VariableInitializer)}
  deriving (Eq, Ord, Read, Show)

_BlockPropertyBody = (Core.Name "hydra/ext/csharp/syntax.BlockPropertyBody")

_BlockPropertyBody_accessors = (Core.Name "accessors")

_BlockPropertyBody_initializer = (Core.Name "initializer")

data RefPropertyBody = 
  RefPropertyBodyBlock RefGetAccessorDeclaration |
  RefPropertyBodyRef VariableReference
  deriving (Eq, Ord, Read, Show)

_RefPropertyBody = (Core.Name "hydra/ext/csharp/syntax.RefPropertyBody")

_RefPropertyBody_block = (Core.Name "block")

_RefPropertyBody_ref = (Core.Name "ref")

data AccessorDeclarations = 
  AccessorDeclarationsGet (Maybe AccessorDeclaration) |
  AccessorDeclarationsSet (Maybe AccessorDeclaration)
  deriving (Eq, Ord, Read, Show)

_AccessorDeclarations = (Core.Name "hydra/ext/csharp/syntax.AccessorDeclarations")

_AccessorDeclarations_get = (Core.Name "get")

_AccessorDeclarations_set = (Core.Name "set")

data AccessorDeclaration = 
  AccessorDeclaration {
    accessorDeclarationAttributes :: (Maybe Attributes),
    accessorDeclarationModifier :: (Maybe AccessorModifier),
    accessorDeclarationBody :: AccessorBody}
  deriving (Eq, Ord, Read, Show)

_AccessorDeclaration = (Core.Name "hydra/ext/csharp/syntax.AccessorDeclaration")

_AccessorDeclaration_attributes = (Core.Name "attributes")

_AccessorDeclaration_modifier = (Core.Name "modifier")

_AccessorDeclaration_body = (Core.Name "body")

data AccessorModifier = 
  AccessorModifierProtected  |
  AccessorModifierInternal  |
  AccessorModifierPrivate  |
  AccessorModifierProtectedInternal  |
  AccessorModifierInternalProtected  |
  AccessorModifierProtectedPrivate  |
  AccessorModifierPrivateProtected 
  deriving (Eq, Ord, Read, Show)

_AccessorModifier = (Core.Name "hydra/ext/csharp/syntax.AccessorModifier")

_AccessorModifier_protected = (Core.Name "protected")

_AccessorModifier_internal = (Core.Name "internal")

_AccessorModifier_private = (Core.Name "private")

_AccessorModifier_protectedInternal = (Core.Name "protectedInternal")

_AccessorModifier_internalProtected = (Core.Name "internalProtected")

_AccessorModifier_protectedPrivate = (Core.Name "protectedPrivate")

_AccessorModifier_privateProtected = (Core.Name "privateProtected")

data AccessorBody = 
  AccessorBodyBlock Block |
  AccessorBodyExpression Expression |
  AccessorBodyEmpty 
  deriving (Eq, Ord, Read, Show)

_AccessorBody = (Core.Name "hydra/ext/csharp/syntax.AccessorBody")

_AccessorBody_block = (Core.Name "block")

_AccessorBody_expression = (Core.Name "expression")

_AccessorBody_empty = (Core.Name "empty")

data RefGetAccessorDeclaration = 
  RefGetAccessorDeclaration {
    refGetAccessorDeclarationAttributes :: (Maybe Attributes),
    refGetAccessorDeclarationModifier :: (Maybe AccessorModifier),
    refGetAccessorDeclarationBody :: RefAccessorBody}
  deriving (Eq, Ord, Read, Show)

_RefGetAccessorDeclaration = (Core.Name "hydra/ext/csharp/syntax.RefGetAccessorDeclaration")

_RefGetAccessorDeclaration_attributes = (Core.Name "attributes")

_RefGetAccessorDeclaration_modifier = (Core.Name "modifier")

_RefGetAccessorDeclaration_body = (Core.Name "body")

data RefAccessorBody = 
  RefAccessorBodyBlock Block |
  RefAccessorBodyRef VariableReference |
  RefAccessorBodyEmpty 
  deriving (Eq, Ord, Read, Show)

_RefAccessorBody = (Core.Name "hydra/ext/csharp/syntax.RefAccessorBody")

_RefAccessorBody_block = (Core.Name "block")

_RefAccessorBody_ref = (Core.Name "ref")

_RefAccessorBody_empty = (Core.Name "empty")

data EventDeclaration = 
  EventDeclarationStandard StandardEventDeclaration |
  EventDeclarationAccessors AccessorsEventDeclaration
  deriving (Eq, Ord, Read, Show)

_EventDeclaration = (Core.Name "hydra/ext/csharp/syntax.EventDeclaration")

_EventDeclaration_standard = (Core.Name "standard")

_EventDeclaration_accessors = (Core.Name "accessors")

data StandardEventDeclaration = 
  StandardEventDeclaration {
    standardEventDeclarationAttributes :: (Maybe Attributes),
    standardEventDeclarationModifiers :: [EventModifier],
    standardEventDeclarationType :: Type,
    standardEventDeclarationDeclarators :: VariableDeclarators}
  deriving (Eq, Ord, Read, Show)

_StandardEventDeclaration = (Core.Name "hydra/ext/csharp/syntax.StandardEventDeclaration")

_StandardEventDeclaration_attributes = (Core.Name "attributes")

_StandardEventDeclaration_modifiers = (Core.Name "modifiers")

_StandardEventDeclaration_type = (Core.Name "type")

_StandardEventDeclaration_declarators = (Core.Name "declarators")

data AccessorsEventDeclaration = 
  AccessorsEventDeclaration {
    accessorsEventDeclarationAttributes :: (Maybe Attributes),
    accessorsEventDeclarationModifiers :: [EventModifier],
    accessorsEventDeclarationType :: Type,
    accessorsEventDeclarationName :: MemberName,
    accessorsEventDeclarationAccessors :: EventAccessorDeclarations}
  deriving (Eq, Ord, Read, Show)

_AccessorsEventDeclaration = (Core.Name "hydra/ext/csharp/syntax.AccessorsEventDeclaration")

_AccessorsEventDeclaration_attributes = (Core.Name "attributes")

_AccessorsEventDeclaration_modifiers = (Core.Name "modifiers")

_AccessorsEventDeclaration_type = (Core.Name "type")

_AccessorsEventDeclaration_name = (Core.Name "name")

_AccessorsEventDeclaration_accessors = (Core.Name "accessors")

data EventModifier = 
  EventModifierNew  |
  EventModifierPublic  |
  EventModifierProtected  |
  EventModifierInternal  |
  EventModifierPrivate  |
  EventModifierStatic  |
  EventModifierVirtual  |
  EventModifierSealed  |
  EventModifierOverride  |
  EventModifierAbstract  |
  EventModifierExtern  |
  EventModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_EventModifier = (Core.Name "hydra/ext/csharp/syntax.EventModifier")

_EventModifier_new = (Core.Name "new")

_EventModifier_public = (Core.Name "public")

_EventModifier_protected = (Core.Name "protected")

_EventModifier_internal = (Core.Name "internal")

_EventModifier_private = (Core.Name "private")

_EventModifier_static = (Core.Name "static")

_EventModifier_virtual = (Core.Name "virtual")

_EventModifier_sealed = (Core.Name "sealed")

_EventModifier_override = (Core.Name "override")

_EventModifier_abstract = (Core.Name "abstract")

_EventModifier_extern = (Core.Name "extern")

_EventModifier_unsafe = (Core.Name "unsafe")

data EventAccessorDeclarations = 
  EventAccessorDeclarationsAdd AddRemoveAccessorDeclaration |
  EventAccessorDeclarationsRemove AddRemoveAccessorDeclaration
  deriving (Eq, Ord, Read, Show)

_EventAccessorDeclarations = (Core.Name "hydra/ext/csharp/syntax.EventAccessorDeclarations")

_EventAccessorDeclarations_add = (Core.Name "add")

_EventAccessorDeclarations_remove = (Core.Name "remove")

data AddRemoveAccessorDeclaration = 
  AddRemoveAccessorDeclaration {
    addRemoveAccessorDeclarationAttributes :: (Maybe Attributes),
    addRemoveAccessorDeclarationBody :: Block}
  deriving (Eq, Ord, Read, Show)

_AddRemoveAccessorDeclaration = (Core.Name "hydra/ext/csharp/syntax.AddRemoveAccessorDeclaration")

_AddRemoveAccessorDeclaration_attributes = (Core.Name "attributes")

_AddRemoveAccessorDeclaration_body = (Core.Name "body")

data IndexerDeclaration = 
  IndexerDeclarationStandard StandardIndexerDeclaration |
  IndexerDeclarationRef RefIndexerDeclaration
  deriving (Eq, Ord, Read, Show)

_IndexerDeclaration = (Core.Name "hydra/ext/csharp/syntax.IndexerDeclaration")

_IndexerDeclaration_standard = (Core.Name "standard")

_IndexerDeclaration_ref = (Core.Name "ref")

data StandardIndexerDeclaration = 
  StandardIndexerDeclaration {
    standardIndexerDeclarationAttributes :: (Maybe Attributes),
    standardIndexerDeclarationModifiers :: [IndexerModifier],
    standardIndexerDeclarationDeclarator :: IndexerDeclarator,
    standardIndexerDeclarationBody :: IndexerBody}
  deriving (Eq, Ord, Read, Show)

_StandardIndexerDeclaration = (Core.Name "hydra/ext/csharp/syntax.StandardIndexerDeclaration")

_StandardIndexerDeclaration_attributes = (Core.Name "attributes")

_StandardIndexerDeclaration_modifiers = (Core.Name "modifiers")

_StandardIndexerDeclaration_declarator = (Core.Name "declarator")

_StandardIndexerDeclaration_body = (Core.Name "body")

data RefIndexerDeclaration = 
  RefIndexerDeclaration {
    refIndexerDeclarationAttributes :: (Maybe Attributes),
    refIndexerDeclarationModifiers :: [IndexerModifier],
    refIndexerDeclarationRefKind :: RefKind,
    refIndexerDeclarationDeclarator :: IndexerDeclarator,
    refIndexerDeclarationBody :: RefIndexerBody}
  deriving (Eq, Ord, Read, Show)

_RefIndexerDeclaration = (Core.Name "hydra/ext/csharp/syntax.RefIndexerDeclaration")

_RefIndexerDeclaration_attributes = (Core.Name "attributes")

_RefIndexerDeclaration_modifiers = (Core.Name "modifiers")

_RefIndexerDeclaration_refKind = (Core.Name "refKind")

_RefIndexerDeclaration_declarator = (Core.Name "declarator")

_RefIndexerDeclaration_body = (Core.Name "body")

data IndexerModifier = 
  IndexerModifierNew  |
  IndexerModifierPublic  |
  IndexerModifierProtected  |
  IndexerModifierInternal  |
  IndexerModifierPrivate  |
  IndexerModifierVirtual  |
  IndexerModifierSealed  |
  IndexerModifierOverride  |
  IndexerModifierAbstract  |
  IndexerModifierExtern  |
  IndexerModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_IndexerModifier = (Core.Name "hydra/ext/csharp/syntax.IndexerModifier")

_IndexerModifier_new = (Core.Name "new")

_IndexerModifier_public = (Core.Name "public")

_IndexerModifier_protected = (Core.Name "protected")

_IndexerModifier_internal = (Core.Name "internal")

_IndexerModifier_private = (Core.Name "private")

_IndexerModifier_virtual = (Core.Name "virtual")

_IndexerModifier_sealed = (Core.Name "sealed")

_IndexerModifier_override = (Core.Name "override")

_IndexerModifier_abstract = (Core.Name "abstract")

_IndexerModifier_extern = (Core.Name "extern")

_IndexerModifier_unsafe = (Core.Name "unsafe")

data IndexerDeclarator = 
  IndexerDeclarator {
    indexerDeclaratorType :: Type,
    indexerDeclaratorInterface :: (Maybe InterfaceType),
    indexerDeclaratorParameters :: FormalParameterList}
  deriving (Eq, Ord, Read, Show)

_IndexerDeclarator = (Core.Name "hydra/ext/csharp/syntax.IndexerDeclarator")

_IndexerDeclarator_type = (Core.Name "type")

_IndexerDeclarator_interface = (Core.Name "interface")

_IndexerDeclarator_parameters = (Core.Name "parameters")

data IndexerBody = 
  IndexerBodyBlock AccessorDeclarations |
  IndexerBodyExpression Expression
  deriving (Eq, Ord, Read, Show)

_IndexerBody = (Core.Name "hydra/ext/csharp/syntax.IndexerBody")

_IndexerBody_block = (Core.Name "block")

_IndexerBody_expression = (Core.Name "expression")

data RefIndexerBody = 
  RefIndexerBodyBlock RefGetAccessorDeclaration |
  RefIndexerBodyRef VariableReference
  deriving (Eq, Ord, Read, Show)

_RefIndexerBody = (Core.Name "hydra/ext/csharp/syntax.RefIndexerBody")

_RefIndexerBody_block = (Core.Name "block")

_RefIndexerBody_ref = (Core.Name "ref")

data OperatorDeclaration = 
  OperatorDeclaration {
    operatorDeclarationAttributes :: (Maybe Attributes),
    operatorDeclarationModifiers :: [OperatorModifier],
    operatorDeclarationDeclarator :: OperatorDeclarator,
    operatorDeclarationBody :: OperatorBody}
  deriving (Eq, Ord, Read, Show)

_OperatorDeclaration = (Core.Name "hydra/ext/csharp/syntax.OperatorDeclaration")

_OperatorDeclaration_attributes = (Core.Name "attributes")

_OperatorDeclaration_modifiers = (Core.Name "modifiers")

_OperatorDeclaration_declarator = (Core.Name "declarator")

_OperatorDeclaration_body = (Core.Name "body")

data OperatorModifier = 
  OperatorModifierPublic  |
  OperatorModifierStatic  |
  OperatorModifierExtern  |
  OperatorModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_OperatorModifier = (Core.Name "hydra/ext/csharp/syntax.OperatorModifier")

_OperatorModifier_public = (Core.Name "public")

_OperatorModifier_static = (Core.Name "static")

_OperatorModifier_extern = (Core.Name "extern")

_OperatorModifier_unsafe = (Core.Name "unsafe")

data OperatorDeclarator = 
  OperatorDeclaratorUnary UnaryOperatorDeclarator |
  OperatorDeclaratorBinary BinaryOperatorDeclarator |
  OperatorDeclaratorConversion ConversionOperatorDeclarator
  deriving (Eq, Ord, Read, Show)

_OperatorDeclarator = (Core.Name "hydra/ext/csharp/syntax.OperatorDeclarator")

_OperatorDeclarator_unary = (Core.Name "unary")

_OperatorDeclarator_binary = (Core.Name "binary")

_OperatorDeclarator_conversion = (Core.Name "conversion")

data UnaryOperatorDeclarator = 
  UnaryOperatorDeclarator {
    unaryOperatorDeclaratorType :: Type,
    unaryOperatorDeclaratorOperator :: OverloadableUnaryOperator,
    unaryOperatorDeclaratorParameter :: FixedParameter}
  deriving (Eq, Ord, Read, Show)

_UnaryOperatorDeclarator = (Core.Name "hydra/ext/csharp/syntax.UnaryOperatorDeclarator")

_UnaryOperatorDeclarator_type = (Core.Name "type")

_UnaryOperatorDeclarator_operator = (Core.Name "operator")

_UnaryOperatorDeclarator_parameter = (Core.Name "parameter")

data OverloadableUnaryOperator = 
  OverloadableUnaryOperatorPlus  |
  OverloadableUnaryOperatorMinus  |
  OverloadableUnaryOperatorNot  |
  OverloadableUnaryOperatorComplement  |
  OverloadableUnaryOperatorIncrement  |
  OverloadableUnaryOperatorDecrement  |
  OverloadableUnaryOperatorTrue  |
  OverloadableUnaryOperatorFalse 
  deriving (Eq, Ord, Read, Show)

_OverloadableUnaryOperator = (Core.Name "hydra/ext/csharp/syntax.OverloadableUnaryOperator")

_OverloadableUnaryOperator_plus = (Core.Name "plus")

_OverloadableUnaryOperator_minus = (Core.Name "minus")

_OverloadableUnaryOperator_not = (Core.Name "not")

_OverloadableUnaryOperator_complement = (Core.Name "complement")

_OverloadableUnaryOperator_increment = (Core.Name "increment")

_OverloadableUnaryOperator_decrement = (Core.Name "decrement")

_OverloadableUnaryOperator_true = (Core.Name "true")

_OverloadableUnaryOperator_false = (Core.Name "false")

data BinaryOperatorDeclarator = 
  BinaryOperatorDeclarator {
    binaryOperatorDeclaratorType :: Type,
    binaryOperatorDeclaratorOperator :: OverloadableBinaryOperator,
    binaryOperatorDeclaratorLeft :: FixedParameter,
    binaryOperatorDeclaratorRight :: FixedParameter}
  deriving (Eq, Ord, Read, Show)

_BinaryOperatorDeclarator = (Core.Name "hydra/ext/csharp/syntax.BinaryOperatorDeclarator")

_BinaryOperatorDeclarator_type = (Core.Name "type")

_BinaryOperatorDeclarator_operator = (Core.Name "operator")

_BinaryOperatorDeclarator_left = (Core.Name "left")

_BinaryOperatorDeclarator_right = (Core.Name "right")

data OverloadableBinaryOperator = 
  OverloadableBinaryOperatorAdd  |
  OverloadableBinaryOperatorSubtract  |
  OverloadableBinaryOperatorMultiply  |
  OverloadableBinaryOperatorDivide  |
  OverloadableBinaryOperatorModulus  |
  OverloadableBinaryOperatorAnd  |
  OverloadableBinaryOperatorOr  |
  OverloadableBinaryOperatorXor  |
  OverloadableBinaryOperatorLeftShift  |
  OverloadableBinaryOperatorRightShift  |
  OverloadableBinaryOperatorEqual  |
  OverloadableBinaryOperatorNotEqual  |
  OverloadableBinaryOperatorGreaterThan  |
  OverloadableBinaryOperatorLessThan  |
  OverloadableBinaryOperatorGreaterThanOrEqual  |
  OverloadableBinaryOperatorLessThanOrEqual 
  deriving (Eq, Ord, Read, Show)

_OverloadableBinaryOperator = (Core.Name "hydra/ext/csharp/syntax.OverloadableBinaryOperator")

_OverloadableBinaryOperator_add = (Core.Name "add")

_OverloadableBinaryOperator_subtract = (Core.Name "subtract")

_OverloadableBinaryOperator_multiply = (Core.Name "multiply")

_OverloadableBinaryOperator_divide = (Core.Name "divide")

_OverloadableBinaryOperator_modulus = (Core.Name "modulus")

_OverloadableBinaryOperator_and = (Core.Name "and")

_OverloadableBinaryOperator_or = (Core.Name "or")

_OverloadableBinaryOperator_xor = (Core.Name "xor")

_OverloadableBinaryOperator_leftShift = (Core.Name "leftShift")

_OverloadableBinaryOperator_rightShift = (Core.Name "rightShift")

_OverloadableBinaryOperator_equal = (Core.Name "equal")

_OverloadableBinaryOperator_notEqual = (Core.Name "notEqual")

_OverloadableBinaryOperator_greaterThan = (Core.Name "greaterThan")

_OverloadableBinaryOperator_lessThan = (Core.Name "lessThan")

_OverloadableBinaryOperator_greaterThanOrEqual = (Core.Name "greaterThanOrEqual")

_OverloadableBinaryOperator_lessThanOrEqual = (Core.Name "lessThanOrEqual")

data ConversionOperatorDeclarator = 
  ConversionOperatorDeclarator {
    conversionOperatorDeclaratorKind :: ConversionKind,
    conversionOperatorDeclaratorType :: Type,
    conversionOperatorDeclaratorParameter :: FixedParameter}
  deriving (Eq, Ord, Read, Show)

_ConversionOperatorDeclarator = (Core.Name "hydra/ext/csharp/syntax.ConversionOperatorDeclarator")

_ConversionOperatorDeclarator_kind = (Core.Name "kind")

_ConversionOperatorDeclarator_type = (Core.Name "type")

_ConversionOperatorDeclarator_parameter = (Core.Name "parameter")

data ConversionKind = 
  ConversionKindImplicit  |
  ConversionKindExplicit 
  deriving (Eq, Ord, Read, Show)

_ConversionKind = (Core.Name "hydra/ext/csharp/syntax.ConversionKind")

_ConversionKind_implicit = (Core.Name "implicit")

_ConversionKind_explicit = (Core.Name "explicit")

data OperatorBody = 
  OperatorBodyBlock Block |
  OperatorBodyExpression Expression |
  OperatorBodyEmpty 
  deriving (Eq, Ord, Read, Show)

_OperatorBody = (Core.Name "hydra/ext/csharp/syntax.OperatorBody")

_OperatorBody_block = (Core.Name "block")

_OperatorBody_expression = (Core.Name "expression")

_OperatorBody_empty = (Core.Name "empty")

data ConstructorDeclaration = 
  ConstructorDeclaration {
    constructorDeclarationAttributes :: (Maybe Attributes),
    constructorDeclarationModifiers :: [ConstructorModifier],
    constructorDeclarationDeclarator :: ConstructorDeclarator,
    constructorDeclarationBody :: ConstructorBody}
  deriving (Eq, Ord, Read, Show)

_ConstructorDeclaration = (Core.Name "hydra/ext/csharp/syntax.ConstructorDeclaration")

_ConstructorDeclaration_attributes = (Core.Name "attributes")

_ConstructorDeclaration_modifiers = (Core.Name "modifiers")

_ConstructorDeclaration_declarator = (Core.Name "declarator")

_ConstructorDeclaration_body = (Core.Name "body")

data ConstructorModifier = 
  ConstructorModifierPublic  |
  ConstructorModifierProtected  |
  ConstructorModifierInternal  |
  ConstructorModifierPrivate  |
  ConstructorModifierExtern  |
  ConstructorModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_ConstructorModifier = (Core.Name "hydra/ext/csharp/syntax.ConstructorModifier")

_ConstructorModifier_public = (Core.Name "public")

_ConstructorModifier_protected = (Core.Name "protected")

_ConstructorModifier_internal = (Core.Name "internal")

_ConstructorModifier_private = (Core.Name "private")

_ConstructorModifier_extern = (Core.Name "extern")

_ConstructorModifier_unsafe = (Core.Name "unsafe")

data ConstructorDeclarator = 
  ConstructorDeclarator {
    constructorDeclaratorName :: Identifier,
    constructorDeclaratorParameters :: (Maybe FormalParameterList),
    constructorDeclaratorInitializer :: (Maybe ConstructorInitializer)}
  deriving (Eq, Ord, Read, Show)

_ConstructorDeclarator = (Core.Name "hydra/ext/csharp/syntax.ConstructorDeclarator")

_ConstructorDeclarator_name = (Core.Name "name")

_ConstructorDeclarator_parameters = (Core.Name "parameters")

_ConstructorDeclarator_initializer = (Core.Name "initializer")

data ConstructorInitializer = 
  ConstructorInitializerBase (Maybe ArgumentList) |
  ConstructorInitializerThis (Maybe ArgumentList)
  deriving (Eq, Ord, Read, Show)

_ConstructorInitializer = (Core.Name "hydra/ext/csharp/syntax.ConstructorInitializer")

_ConstructorInitializer_base = (Core.Name "base")

_ConstructorInitializer_this = (Core.Name "this")

data ConstructorBody = 
  ConstructorBodyBlock Block |
  ConstructorBodyExpression Expression |
  ConstructorBodyEmpty 
  deriving (Eq, Ord, Read, Show)

_ConstructorBody = (Core.Name "hydra/ext/csharp/syntax.ConstructorBody")

_ConstructorBody_block = (Core.Name "block")

_ConstructorBody_expression = (Core.Name "expression")

_ConstructorBody_empty = (Core.Name "empty")

data StaticConstructorDeclaration = 
  StaticConstructorDeclaration {
    staticConstructorDeclarationAttributes :: (Maybe Attributes),
    staticConstructorDeclarationModifiers :: StaticConstructorModifiers,
    staticConstructorDeclarationName :: Identifier,
    staticConstructorDeclarationBody :: StaticConstructorBody}
  deriving (Eq, Ord, Read, Show)

_StaticConstructorDeclaration = (Core.Name "hydra/ext/csharp/syntax.StaticConstructorDeclaration")

_StaticConstructorDeclaration_attributes = (Core.Name "attributes")

_StaticConstructorDeclaration_modifiers = (Core.Name "modifiers")

_StaticConstructorDeclaration_name = (Core.Name "name")

_StaticConstructorDeclaration_body = (Core.Name "body")

data StaticConstructorModifiers = 
  StaticConstructorModifiers {
    staticConstructorModifiersExtern :: Bool,
    staticConstructorModifiersUnsafe :: Bool}
  deriving (Eq, Ord, Read, Show)

_StaticConstructorModifiers = (Core.Name "hydra/ext/csharp/syntax.StaticConstructorModifiers")

_StaticConstructorModifiers_extern = (Core.Name "extern")

_StaticConstructorModifiers_unsafe = (Core.Name "unsafe")

data StaticConstructorBody = 
  StaticConstructorBodyBlock Block |
  StaticConstructorBodyExpression Expression |
  StaticConstructorBodyEmpty 
  deriving (Eq, Ord, Read, Show)

_StaticConstructorBody = (Core.Name "hydra/ext/csharp/syntax.StaticConstructorBody")

_StaticConstructorBody_block = (Core.Name "block")

_StaticConstructorBody_expression = (Core.Name "expression")

_StaticConstructorBody_empty = (Core.Name "empty")

data FinalizerDeclaration = 
  FinalizerDeclaration {
    finalizerDeclarationAttributes :: (Maybe Attributes),
    finalizerDeclarationExtern :: Bool,
    finalizerDeclarationUnsafe :: Bool,
    finalizerDeclarationName :: Identifier,
    finalizerDeclarationBody :: FinalizerBody}
  deriving (Eq, Ord, Read, Show)

_FinalizerDeclaration = (Core.Name "hydra/ext/csharp/syntax.FinalizerDeclaration")

_FinalizerDeclaration_attributes = (Core.Name "attributes")

_FinalizerDeclaration_extern = (Core.Name "extern")

_FinalizerDeclaration_unsafe = (Core.Name "unsafe")

_FinalizerDeclaration_name = (Core.Name "name")

_FinalizerDeclaration_body = (Core.Name "body")

data FinalizerBody = 
  FinalizerBodyBlock Block |
  FinalizerBodyExpression Expression |
  FinalizerBodyEmpty 
  deriving (Eq, Ord, Read, Show)

_FinalizerBody = (Core.Name "hydra/ext/csharp/syntax.FinalizerBody")

_FinalizerBody_block = (Core.Name "block")

_FinalizerBody_expression = (Core.Name "expression")

_FinalizerBody_empty = (Core.Name "empty")

data StructDeclaration = 
  StructDeclaration {
    structDeclarationAttributes :: (Maybe Attributes),
    structDeclarationModifiers :: [StructModifier],
    structDeclarationRef :: Bool,
    structDeclarationPartial :: Bool,
    structDeclarationName :: Identifier,
    structDeclarationParameters :: (Maybe TypeParameterList),
    structDeclarationInterfaces :: [InterfaceType],
    structDeclarationConstraints :: [TypeParameterConstraintsClause],
    structDeclarationBody :: [StructMemberDeclaration]}
  deriving (Eq, Ord, Read, Show)

_StructDeclaration = (Core.Name "hydra/ext/csharp/syntax.StructDeclaration")

_StructDeclaration_attributes = (Core.Name "attributes")

_StructDeclaration_modifiers = (Core.Name "modifiers")

_StructDeclaration_ref = (Core.Name "ref")

_StructDeclaration_partial = (Core.Name "partial")

_StructDeclaration_name = (Core.Name "name")

_StructDeclaration_parameters = (Core.Name "parameters")

_StructDeclaration_interfaces = (Core.Name "interfaces")

_StructDeclaration_constraints = (Core.Name "constraints")

_StructDeclaration_body = (Core.Name "body")

data StructModifier = 
  StructModifierNew  |
  StructModifierPublic  |
  StructModifierProtected  |
  StructModifierInternal  |
  StructModifierPrivate  |
  StructModifierReadonly  |
  StructModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_StructModifier = (Core.Name "hydra/ext/csharp/syntax.StructModifier")

_StructModifier_new = (Core.Name "new")

_StructModifier_public = (Core.Name "public")

_StructModifier_protected = (Core.Name "protected")

_StructModifier_internal = (Core.Name "internal")

_StructModifier_private = (Core.Name "private")

_StructModifier_readonly = (Core.Name "readonly")

_StructModifier_unsafe = (Core.Name "unsafe")

data StructMemberDeclaration = 
  StructMemberDeclarationConstant ConstantDeclaration |
  StructMemberDeclarationField FieldDeclaration |
  StructMemberDeclarationMethod MethodDeclaration |
  StructMemberDeclarationProperty PropertyDeclaration |
  StructMemberDeclarationEvent EventDeclaration |
  StructMemberDeclarationIndexer IndexerDeclaration |
  StructMemberDeclarationOperator OperatorDeclaration |
  StructMemberDeclarationConstructor ConstructorDeclaration |
  StructMemberDeclarationStaticConstructor StaticConstructorDeclaration |
  StructMemberDeclarationType TypeDeclaration |
  StructMemberDeclarationFixedSizeBuffer FixedSizeBufferDeclaration
  deriving (Eq, Ord, Read, Show)

_StructMemberDeclaration = (Core.Name "hydra/ext/csharp/syntax.StructMemberDeclaration")

_StructMemberDeclaration_constant = (Core.Name "constant")

_StructMemberDeclaration_field = (Core.Name "field")

_StructMemberDeclaration_method = (Core.Name "method")

_StructMemberDeclaration_property = (Core.Name "property")

_StructMemberDeclaration_event = (Core.Name "event")

_StructMemberDeclaration_indexer = (Core.Name "indexer")

_StructMemberDeclaration_operator = (Core.Name "operator")

_StructMemberDeclaration_constructor = (Core.Name "constructor")

_StructMemberDeclaration_staticConstructor = (Core.Name "staticConstructor")

_StructMemberDeclaration_type = (Core.Name "type")

_StructMemberDeclaration_fixedSizeBuffer = (Core.Name "fixedSizeBuffer")

newtype ArrayInitializer = 
  ArrayInitializer {
    unArrayInitializer :: [VariableInitializer]}
  deriving (Eq, Ord, Read, Show)

_ArrayInitializer = (Core.Name "hydra/ext/csharp/syntax.ArrayInitializer")

data VariableInitializer = 
  VariableInitializerExpression Expression |
  VariableInitializerArray ArrayInitializer
  deriving (Eq, Ord, Read, Show)

_VariableInitializer = (Core.Name "hydra/ext/csharp/syntax.VariableInitializer")

_VariableInitializer_expression = (Core.Name "expression")

_VariableInitializer_array = (Core.Name "array")

data InterfaceDeclaration = 
  InterfaceDeclaration {
    interfaceDeclarationAttributes :: (Maybe Attributes),
    interfaceDeclarationModifiers :: [InterfaceModifier],
    interfaceDeclarationPartial :: Bool,
    interfaceDeclarationName :: Identifier,
    interfaceDeclarationParameters :: (Maybe VariantTypeParameters),
    interfaceDeclarationBase :: [InterfaceType],
    interfaceDeclarationConstraints :: [TypeParameterConstraintsClause],
    interfaceDeclarationBody :: [InterfaceMemberDeclaration]}
  deriving (Eq, Ord, Read, Show)

_InterfaceDeclaration = (Core.Name "hydra/ext/csharp/syntax.InterfaceDeclaration")

_InterfaceDeclaration_attributes = (Core.Name "attributes")

_InterfaceDeclaration_modifiers = (Core.Name "modifiers")

_InterfaceDeclaration_partial = (Core.Name "partial")

_InterfaceDeclaration_name = (Core.Name "name")

_InterfaceDeclaration_parameters = (Core.Name "parameters")

_InterfaceDeclaration_base = (Core.Name "base")

_InterfaceDeclaration_constraints = (Core.Name "constraints")

_InterfaceDeclaration_body = (Core.Name "body")

data InterfaceModifier = 
  InterfaceModifierNew  |
  InterfaceModifierPublic  |
  InterfaceModifierProtected  |
  InterfaceModifierInternal  |
  InterfaceModifierPrivate  |
  InterfaceModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_InterfaceModifier = (Core.Name "hydra/ext/csharp/syntax.InterfaceModifier")

_InterfaceModifier_new = (Core.Name "new")

_InterfaceModifier_public = (Core.Name "public")

_InterfaceModifier_protected = (Core.Name "protected")

_InterfaceModifier_internal = (Core.Name "internal")

_InterfaceModifier_private = (Core.Name "private")

_InterfaceModifier_unsafe = (Core.Name "unsafe")

newtype VariantTypeParameters = 
  VariantTypeParameters {
    unVariantTypeParameters :: [VariantTypeParameter]}
  deriving (Eq, Ord, Read, Show)

_VariantTypeParameters = (Core.Name "hydra/ext/csharp/syntax.VariantTypeParameters")

data VariantTypeParameter = 
  VariantTypeParameter {
    variantTypeParameterAttributes :: (Maybe Attributes),
    variantTypeParameterVariance :: (Maybe VarianceAnnotation),
    variantTypeParameterParameter :: TypeParameter}
  deriving (Eq, Ord, Read, Show)

_VariantTypeParameter = (Core.Name "hydra/ext/csharp/syntax.VariantTypeParameter")

_VariantTypeParameter_attributes = (Core.Name "attributes")

_VariantTypeParameter_variance = (Core.Name "variance")

_VariantTypeParameter_parameter = (Core.Name "parameter")

data VarianceAnnotation = 
  VarianceAnnotationIn  |
  VarianceAnnotationOut 
  deriving (Eq, Ord, Read, Show)

_VarianceAnnotation = (Core.Name "hydra/ext/csharp/syntax.VarianceAnnotation")

_VarianceAnnotation_in = (Core.Name "in")

_VarianceAnnotation_out = (Core.Name "out")

data InterfaceMemberDeclaration = 
  InterfaceMemberDeclarationMethod InterfaceMethodDeclaration |
  InterfaceMemberDeclarationProperty InterfacePropertyDeclaration |
  InterfaceMemberDeclarationEvent InterfaceEventDeclaration |
  InterfaceMemberDeclarationIndexer InterfaceIndexerDeclaration
  deriving (Eq, Ord, Read, Show)

_InterfaceMemberDeclaration = (Core.Name "hydra/ext/csharp/syntax.InterfaceMemberDeclaration")

_InterfaceMemberDeclaration_method = (Core.Name "method")

_InterfaceMemberDeclaration_property = (Core.Name "property")

_InterfaceMemberDeclaration_event = (Core.Name "event")

_InterfaceMemberDeclaration_indexer = (Core.Name "indexer")

data InterfaceMethodDeclaration = 
  InterfaceMethodDeclaration {
    interfaceMethodDeclarationAttributes :: (Maybe Attributes),
    interfaceMethodDeclarationNew :: Bool,
    interfaceMethodDeclarationReturnType :: ReturnType,
    interfaceMethodDeclarationRefKind :: (Maybe RefKind),
    interfaceMethodDeclarationHeader :: InterfaceMethodHeader}
  deriving (Eq, Ord, Read, Show)

_InterfaceMethodDeclaration = (Core.Name "hydra/ext/csharp/syntax.InterfaceMethodDeclaration")

_InterfaceMethodDeclaration_attributes = (Core.Name "attributes")

_InterfaceMethodDeclaration_new = (Core.Name "new")

_InterfaceMethodDeclaration_returnType = (Core.Name "returnType")

_InterfaceMethodDeclaration_refKind = (Core.Name "refKind")

_InterfaceMethodDeclaration_header = (Core.Name "header")

data InterfaceMethodHeader = 
  InterfaceMethodHeader {
    interfaceMethodHeaderName :: Identifier,
    interfaceMethodHeaderParameters :: (Maybe FormalParameterList),
    interfaceMethodHeaderTypeParameters :: (Maybe TypeParameterList),
    interfaceMethodHeaderConstraints :: [TypeParameterConstraintsClause]}
  deriving (Eq, Ord, Read, Show)

_InterfaceMethodHeader = (Core.Name "hydra/ext/csharp/syntax.InterfaceMethodHeader")

_InterfaceMethodHeader_name = (Core.Name "name")

_InterfaceMethodHeader_parameters = (Core.Name "parameters")

_InterfaceMethodHeader_typeParameters = (Core.Name "typeParameters")

_InterfaceMethodHeader_constraints = (Core.Name "constraints")

data InterfacePropertyDeclaration = 
  InterfacePropertyDeclaration {
    interfacePropertyDeclarationAttributes :: (Maybe Attributes),
    interfacePropertyDeclarationNew :: Bool,
    interfacePropertyDeclarationRefKind :: (Maybe RefKind),
    interfacePropertyDeclarationType :: Type,
    interfacePropertyDeclarationName :: Identifier,
    interfacePropertyDeclarationAccessors :: InterfaceAccessors}
  deriving (Eq, Ord, Read, Show)

_InterfacePropertyDeclaration = (Core.Name "hydra/ext/csharp/syntax.InterfacePropertyDeclaration")

_InterfacePropertyDeclaration_attributes = (Core.Name "attributes")

_InterfacePropertyDeclaration_new = (Core.Name "new")

_InterfacePropertyDeclaration_refKind = (Core.Name "refKind")

_InterfacePropertyDeclaration_type = (Core.Name "type")

_InterfacePropertyDeclaration_name = (Core.Name "name")

_InterfacePropertyDeclaration_accessors = (Core.Name "accessors")

data InterfaceAccessors = 
  InterfaceAccessors {
    interfaceAccessorsAttributes :: (Maybe Attributes),
    interfaceAccessorsGet :: (Maybe Attributes),
    interfaceAccessorsSet :: (Maybe Attributes)}
  deriving (Eq, Ord, Read, Show)

_InterfaceAccessors = (Core.Name "hydra/ext/csharp/syntax.InterfaceAccessors")

_InterfaceAccessors_attributes = (Core.Name "attributes")

_InterfaceAccessors_get = (Core.Name "get")

_InterfaceAccessors_set = (Core.Name "set")

data InterfaceEventDeclaration = 
  InterfaceEventDeclaration {
    interfaceEventDeclarationAttributes :: (Maybe Attributes),
    interfaceEventDeclarationNew :: Bool,
    interfaceEventDeclarationType :: Type,
    interfaceEventDeclarationName :: Identifier}
  deriving (Eq, Ord, Read, Show)

_InterfaceEventDeclaration = (Core.Name "hydra/ext/csharp/syntax.InterfaceEventDeclaration")

_InterfaceEventDeclaration_attributes = (Core.Name "attributes")

_InterfaceEventDeclaration_new = (Core.Name "new")

_InterfaceEventDeclaration_type = (Core.Name "type")

_InterfaceEventDeclaration_name = (Core.Name "name")

data InterfaceIndexerDeclaration = 
  InterfaceIndexerDeclaration {
    interfaceIndexerDeclarationAttributes :: (Maybe Attributes),
    interfaceIndexerDeclarationNew :: Bool,
    interfaceIndexerDeclarationRefKind :: (Maybe RefKind),
    interfaceIndexerDeclarationType :: Type,
    interfaceIndexerDeclarationParameters :: FormalParameterList,
    interfaceIndexerDeclarationAccessors :: InterfaceAccessors}
  deriving (Eq, Ord, Read, Show)

_InterfaceIndexerDeclaration = (Core.Name "hydra/ext/csharp/syntax.InterfaceIndexerDeclaration")

_InterfaceIndexerDeclaration_attributes = (Core.Name "attributes")

_InterfaceIndexerDeclaration_new = (Core.Name "new")

_InterfaceIndexerDeclaration_refKind = (Core.Name "refKind")

_InterfaceIndexerDeclaration_type = (Core.Name "type")

_InterfaceIndexerDeclaration_parameters = (Core.Name "parameters")

_InterfaceIndexerDeclaration_accessors = (Core.Name "accessors")

data EnumDeclaration = 
  EnumDeclaration {
    enumDeclarationAttributes :: (Maybe Attributes),
    enumDeclarationModifiers :: [EnumModifier],
    enumDeclarationName :: Identifier,
    enumDeclarationBase :: (Maybe EnumBase),
    enumDeclarationBody :: (Maybe EnumBody)}
  deriving (Eq, Ord, Read, Show)

_EnumDeclaration = (Core.Name "hydra/ext/csharp/syntax.EnumDeclaration")

_EnumDeclaration_attributes = (Core.Name "attributes")

_EnumDeclaration_modifiers = (Core.Name "modifiers")

_EnumDeclaration_name = (Core.Name "name")

_EnumDeclaration_base = (Core.Name "base")

_EnumDeclaration_body = (Core.Name "body")

data EnumBase = 
  EnumBaseType IntegralType |
  EnumBaseName TypeName
  deriving (Eq, Ord, Read, Show)

_EnumBase = (Core.Name "hydra/ext/csharp/syntax.EnumBase")

_EnumBase_type = (Core.Name "type")

_EnumBase_name = (Core.Name "name")

newtype EnumBody = 
  EnumBody {
    unEnumBody :: [EnumMemberDeclaration]}
  deriving (Eq, Ord, Read, Show)

_EnumBody = (Core.Name "hydra/ext/csharp/syntax.EnumBody")

data EnumModifier = 
  EnumModifierNew  |
  EnumModifierPublic  |
  EnumModifierProtected  |
  EnumModifierInternal  |
  EnumModifierPrivate 
  deriving (Eq, Ord, Read, Show)

_EnumModifier = (Core.Name "hydra/ext/csharp/syntax.EnumModifier")

_EnumModifier_new = (Core.Name "new")

_EnumModifier_public = (Core.Name "public")

_EnumModifier_protected = (Core.Name "protected")

_EnumModifier_internal = (Core.Name "internal")

_EnumModifier_private = (Core.Name "private")

data EnumMemberDeclaration = 
  EnumMemberDeclaration {
    enumMemberDeclarationAttributes :: (Maybe Attributes),
    enumMemberDeclarationName :: Identifier,
    enumMemberDeclarationValue :: (Maybe ConstantExpression)}
  deriving (Eq, Ord, Read, Show)

_EnumMemberDeclaration = (Core.Name "hydra/ext/csharp/syntax.EnumMemberDeclaration")

_EnumMemberDeclaration_attributes = (Core.Name "attributes")

_EnumMemberDeclaration_name = (Core.Name "name")

_EnumMemberDeclaration_value = (Core.Name "value")

data DelegateDeclaration = 
  DelegateDeclaration {
    delegateDeclarationAttributes :: (Maybe Attributes),
    delegateDeclarationModifiers :: [DelegateModifier],
    delegateDeclarationReturnType :: ReturnType,
    delegateDeclarationRefKind :: (Maybe RefKind),
    delegateDeclarationRefReturnType :: (Maybe Type),
    delegateDeclarationHeader :: DelegateHeader}
  deriving (Eq, Ord, Read, Show)

_DelegateDeclaration = (Core.Name "hydra/ext/csharp/syntax.DelegateDeclaration")

_DelegateDeclaration_attributes = (Core.Name "attributes")

_DelegateDeclaration_modifiers = (Core.Name "modifiers")

_DelegateDeclaration_returnType = (Core.Name "returnType")

_DelegateDeclaration_refKind = (Core.Name "refKind")

_DelegateDeclaration_refReturnType = (Core.Name "refReturnType")

_DelegateDeclaration_header = (Core.Name "header")

data DelegateHeader = 
  DelegateHeader {
    delegateHeaderName :: Identifier,
    delegateHeaderTypeParameters :: (Maybe VariantTypeParameters),
    delegateHeaderParameters :: (Maybe FormalParameterList),
    delegateHeaderConstraints :: [TypeParameterConstraintsClause]}
  deriving (Eq, Ord, Read, Show)

_DelegateHeader = (Core.Name "hydra/ext/csharp/syntax.DelegateHeader")

_DelegateHeader_name = (Core.Name "name")

_DelegateHeader_typeParameters = (Core.Name "typeParameters")

_DelegateHeader_parameters = (Core.Name "parameters")

_DelegateHeader_constraints = (Core.Name "constraints")

data DelegateModifier = 
  DelegateModifierNew  |
  DelegateModifierPublic  |
  DelegateModifierProtected  |
  DelegateModifierInternal  |
  DelegateModifierPrivate  |
  DelegateModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_DelegateModifier = (Core.Name "hydra/ext/csharp/syntax.DelegateModifier")

_DelegateModifier_new = (Core.Name "new")

_DelegateModifier_public = (Core.Name "public")

_DelegateModifier_protected = (Core.Name "protected")

_DelegateModifier_internal = (Core.Name "internal")

_DelegateModifier_private = (Core.Name "private")

_DelegateModifier_unsafe = (Core.Name "unsafe")

data GlobalAttributeSection = 
  GlobalAttributeSection {
    globalAttributeSectionTarget :: Identifier,
    globalAttributeSectionAttributes :: AttributeList}
  deriving (Eq, Ord, Read, Show)

_GlobalAttributeSection = (Core.Name "hydra/ext/csharp/syntax.GlobalAttributeSection")

_GlobalAttributeSection_target = (Core.Name "target")

_GlobalAttributeSection_attributes = (Core.Name "attributes")

newtype Attributes = 
  Attributes {
    unAttributes :: [AttributeSection]}
  deriving (Eq, Ord, Read, Show)

_Attributes = (Core.Name "hydra/ext/csharp/syntax.Attributes")

data AttributeSection = 
  AttributeSection {
    attributeSectionTarget :: (Maybe AttributeTarget),
    attributeSectionAttributes :: AttributeList}
  deriving (Eq, Ord, Read, Show)

_AttributeSection = (Core.Name "hydra/ext/csharp/syntax.AttributeSection")

_AttributeSection_target = (Core.Name "target")

_AttributeSection_attributes = (Core.Name "attributes")

data AttributeTarget = 
  AttributeTargetIdentifier Identifier |
  AttributeTargetKeyword Keyword
  deriving (Eq, Ord, Read, Show)

_AttributeTarget = (Core.Name "hydra/ext/csharp/syntax.AttributeTarget")

_AttributeTarget_identifier = (Core.Name "identifier")

_AttributeTarget_keyword = (Core.Name "keyword")

newtype AttributeList = 
  AttributeList {
    unAttributeList :: [Attribute]}
  deriving (Eq, Ord, Read, Show)

_AttributeList = (Core.Name "hydra/ext/csharp/syntax.AttributeList")

data Attribute = 
  Attribute {
    attributeName :: AttributeName,
    attributeArguments :: (Maybe AttributeArguments)}
  deriving (Eq, Ord, Read, Show)

_Attribute = (Core.Name "hydra/ext/csharp/syntax.Attribute")

_Attribute_name = (Core.Name "name")

_Attribute_arguments = (Core.Name "arguments")

newtype AttributeName = 
  AttributeName {
    unAttributeName :: TypeName}
  deriving (Eq, Ord, Read, Show)

_AttributeName = (Core.Name "hydra/ext/csharp/syntax.AttributeName")

data AttributeArguments = 
  AttributeArguments {
    attributeArgumentsPositonal :: (Maybe PositionalArgumentList),
    attributeArgumentsNamed :: (Maybe NamedArgumentList)}
  deriving (Eq, Ord, Read, Show)

_AttributeArguments = (Core.Name "hydra/ext/csharp/syntax.AttributeArguments")

_AttributeArguments_positonal = (Core.Name "positonal")

_AttributeArguments_named = (Core.Name "named")

newtype PositionalArgumentList = 
  PositionalArgumentList {
    unPositionalArgumentList :: [PositionalArgument]}
  deriving (Eq, Ord, Read, Show)

_PositionalArgumentList = (Core.Name "hydra/ext/csharp/syntax.PositionalArgumentList")

data PositionalArgument = 
  PositionalArgument {
    positionalArgumentName :: (Maybe Identifier),
    positionalArgumentValue :: AttributeArgumentExpression}
  deriving (Eq, Ord, Read, Show)

_PositionalArgument = (Core.Name "hydra/ext/csharp/syntax.PositionalArgument")

_PositionalArgument_name = (Core.Name "name")

_PositionalArgument_value = (Core.Name "value")

newtype NamedArgumentList = 
  NamedArgumentList {
    unNamedArgumentList :: [NamedArgument]}
  deriving (Eq, Ord, Read, Show)

_NamedArgumentList = (Core.Name "hydra/ext/csharp/syntax.NamedArgumentList")

data NamedArgument = 
  NamedArgument {
    namedArgumentName :: Identifier,
    namedArgumentValue :: AttributeArgumentExpression}
  deriving (Eq, Ord, Read, Show)

_NamedArgument = (Core.Name "hydra/ext/csharp/syntax.NamedArgument")

_NamedArgument_name = (Core.Name "name")

_NamedArgument_value = (Core.Name "value")

newtype AttributeArgumentExpression = 
  AttributeArgumentExpression {
    unAttributeArgumentExpression :: NonAssignmentExpression}
  deriving (Eq, Ord, Read, Show)

_AttributeArgumentExpression = (Core.Name "hydra/ext/csharp/syntax.AttributeArgumentExpression")

data PointerType = 
  PointerTypeValueType (Maybe ValueType) |
  PointerTypePointerDepth Int
  deriving (Eq, Ord, Read, Show)

_PointerType = (Core.Name "hydra/ext/csharp/syntax.PointerType")

_PointerType_valueType = (Core.Name "valueType")

_PointerType_pointerDepth = (Core.Name "pointerDepth")

data PointerMemberAccess = 
  PointerMemberAccess {
    pointerMemberAccessPointer :: PrimaryExpression,
    pointerMemberAccessMember :: Identifier,
    pointerMemberAccessTypeArguments :: (Maybe TypeArgumentList)}
  deriving (Eq, Ord, Read, Show)

_PointerMemberAccess = (Core.Name "hydra/ext/csharp/syntax.PointerMemberAccess")

_PointerMemberAccess_pointer = (Core.Name "pointer")

_PointerMemberAccess_member = (Core.Name "member")

_PointerMemberAccess_typeArguments = (Core.Name "typeArguments")

data PointerElementAccess = 
  PointerElementAccess {
    pointerElementAccessPointer :: PrimaryNoArrayCreationExpression,
    pointerElementAccessIndex :: Expression}
  deriving (Eq, Ord, Read, Show)

_PointerElementAccess = (Core.Name "hydra/ext/csharp/syntax.PointerElementAccess")

_PointerElementAccess_pointer = (Core.Name "pointer")

_PointerElementAccess_index = (Core.Name "index")

data FixedStatement = 
  FixedStatement {
    fixedStatementPointerType :: PointerType,
    fixedStatementDeclarators :: [FixedPointerDeclarator],
    fixedStatementStatement :: EmbeddedStatement}
  deriving (Eq, Ord, Read, Show)

_FixedStatement = (Core.Name "hydra/ext/csharp/syntax.FixedStatement")

_FixedStatement_pointerType = (Core.Name "pointerType")

_FixedStatement_declarators = (Core.Name "declarators")

_FixedStatement_statement = (Core.Name "statement")

data FixedPointerDeclarator = 
  FixedPointerDeclaratorReference VariableReference |
  FixedPointerDeclaratorExpression Expression
  deriving (Eq, Ord, Read, Show)

_FixedPointerDeclarator = (Core.Name "hydra/ext/csharp/syntax.FixedPointerDeclarator")

_FixedPointerDeclarator_reference = (Core.Name "reference")

_FixedPointerDeclarator_expression = (Core.Name "expression")

data FixedSizeBufferDeclaration = 
  FixedSizeBufferDeclaration {
    fixedSizeBufferDeclarationAttributes :: (Maybe Attributes),
    fixedSizeBufferDeclarationModifiers :: [FixedSizeBufferModifier],
    fixedSizeBufferDeclarationElementType :: Type,
    fixedSizeBufferDeclarationDeclarators :: [FixedSizeBufferDeclarator]}
  deriving (Eq, Ord, Read, Show)

_FixedSizeBufferDeclaration = (Core.Name "hydra/ext/csharp/syntax.FixedSizeBufferDeclaration")

_FixedSizeBufferDeclaration_attributes = (Core.Name "attributes")

_FixedSizeBufferDeclaration_modifiers = (Core.Name "modifiers")

_FixedSizeBufferDeclaration_elementType = (Core.Name "elementType")

_FixedSizeBufferDeclaration_declarators = (Core.Name "declarators")

data FixedSizeBufferModifier = 
  FixedSizeBufferModifierNew  |
  FixedSizeBufferModifierPublic  |
  FixedSizeBufferModifierInternal  |
  FixedSizeBufferModifierPrivate  |
  FixedSizeBufferModifierUnsafe 
  deriving (Eq, Ord, Read, Show)

_FixedSizeBufferModifier = (Core.Name "hydra/ext/csharp/syntax.FixedSizeBufferModifier")

_FixedSizeBufferModifier_new = (Core.Name "new")

_FixedSizeBufferModifier_public = (Core.Name "public")

_FixedSizeBufferModifier_internal = (Core.Name "internal")

_FixedSizeBufferModifier_private = (Core.Name "private")

_FixedSizeBufferModifier_unsafe = (Core.Name "unsafe")

data FixedSizeBufferDeclarator = 
  FixedSizeBufferDeclarator {
    fixedSizeBufferDeclaratorName :: Identifier,
    fixedSizeBufferDeclaratorSize :: ConstantExpression}
  deriving (Eq, Ord, Read, Show)

_FixedSizeBufferDeclarator = (Core.Name "hydra/ext/csharp/syntax.FixedSizeBufferDeclarator")

_FixedSizeBufferDeclarator_name = (Core.Name "name")

_FixedSizeBufferDeclarator_size = (Core.Name "size")