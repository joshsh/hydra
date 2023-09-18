-- | A GraphQL model. Based on the (extended) BNF at:
-- |   https://spec.graphql.org/draft/#sec-Appendix-Grammar-Summary

module Hydra.Langs.Graphql.Syntax where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

newtype Name = 
  Name {
    unName :: String}
  deriving (Eq, Ord, Read, Show)

_Name = (Core.Name "hydra/langs/graphql/syntax.Name")

newtype IntValue = 
  IntValue {
    unIntValue :: String}
  deriving (Eq, Ord, Read, Show)

_IntValue = (Core.Name "hydra/langs/graphql/syntax.IntValue")

newtype FloatValue = 
  FloatValue {
    unFloatValue :: String}
  deriving (Eq, Ord, Read, Show)

_FloatValue = (Core.Name "hydra/langs/graphql/syntax.FloatValue")

newtype StringValue = 
  StringValue {
    unStringValue :: String}
  deriving (Eq, Ord, Read, Show)

_StringValue = (Core.Name "hydra/langs/graphql/syntax.StringValue")

newtype Document = 
  Document {
    unDocument :: [Definition]}
  deriving (Eq, Ord, Read, Show)

_Document = (Core.Name "hydra/langs/graphql/syntax.Document")

data Definition = 
  DefinitionExecutable ExecutableDefinition |
  DefinitionTypeSystem TypeSystemDefinitionOrExtension
  deriving (Eq, Ord, Read, Show)

_Definition = (Core.Name "hydra/langs/graphql/syntax.Definition")

_Definition_executable = (Core.FieldName "executable")

_Definition_typeSystem = (Core.FieldName "typeSystem")

newtype ExecutableDocument = 
  ExecutableDocument {
    unExecutableDocument :: [ExecutableDefinition]}
  deriving (Eq, Ord, Read, Show)

_ExecutableDocument = (Core.Name "hydra/langs/graphql/syntax.ExecutableDocument")

data ExecutableDefinition = 
  ExecutableDefinitionOperation OperationDefinition |
  ExecutableDefinitionFragment FragmentDefinition
  deriving (Eq, Ord, Read, Show)

_ExecutableDefinition = (Core.Name "hydra/langs/graphql/syntax.ExecutableDefinition")

_ExecutableDefinition_operation = (Core.FieldName "operation")

_ExecutableDefinition_fragment = (Core.FieldName "fragment")

data OperationDefinition = 
  OperationDefinitionSequence OperationDefinition_Sequence |
  OperationDefinitionSelectionSet SelectionSet
  deriving (Eq, Ord, Read, Show)

_OperationDefinition = (Core.Name "hydra/langs/graphql/syntax.OperationDefinition")

_OperationDefinition_sequence = (Core.FieldName "sequence")

_OperationDefinition_selectionSet = (Core.FieldName "selectionSet")

data OperationDefinition_Sequence = 
  OperationDefinition_Sequence {
    operationDefinition_SequenceOperationType :: OperationType,
    operationDefinition_SequenceName :: (Maybe Name),
    operationDefinition_SequenceVariablesDefinition :: (Maybe VariablesDefinition),
    operationDefinition_SequenceDirectives :: (Maybe Directives),
    operationDefinition_SequenceSelectionSet :: SelectionSet}
  deriving (Eq, Ord, Read, Show)

_OperationDefinition_Sequence = (Core.Name "hydra/langs/graphql/syntax.OperationDefinition.Sequence")

_OperationDefinition_Sequence_operationType = (Core.FieldName "operationType")

_OperationDefinition_Sequence_name = (Core.FieldName "name")

_OperationDefinition_Sequence_variablesDefinition = (Core.FieldName "variablesDefinition")

_OperationDefinition_Sequence_directives = (Core.FieldName "directives")

_OperationDefinition_Sequence_selectionSet = (Core.FieldName "selectionSet")

data OperationType = 
  OperationTypeQuery  |
  OperationTypeMutation  |
  OperationTypeSubscription 
  deriving (Eq, Ord, Read, Show)

_OperationType = (Core.Name "hydra/langs/graphql/syntax.OperationType")

_OperationType_query = (Core.FieldName "query")

_OperationType_mutation = (Core.FieldName "mutation")

_OperationType_subscription = (Core.FieldName "subscription")

newtype SelectionSet = 
  SelectionSet {
    unSelectionSet :: [Selection]}
  deriving (Eq, Ord, Read, Show)

_SelectionSet = (Core.Name "hydra/langs/graphql/syntax.SelectionSet")

data Selection = 
  SelectionField Field |
  SelectionFragmentSpread FragmentSpread |
  SelectionInlineFragment InlineFragment
  deriving (Eq, Ord, Read, Show)

_Selection = (Core.Name "hydra/langs/graphql/syntax.Selection")

_Selection_field = (Core.FieldName "field")

_Selection_fragmentSpread = (Core.FieldName "fragmentSpread")

_Selection_inlineFragment = (Core.FieldName "inlineFragment")

data Field = 
  Field {
    fieldAlias :: (Maybe Alias),
    fieldName :: Name,
    fieldArguments :: (Maybe Arguments),
    fieldDirectives :: (Maybe Directives),
    fieldSelectionSet :: (Maybe SelectionSet)}
  deriving (Eq, Ord, Read, Show)

_Field = (Core.Name "hydra/langs/graphql/syntax.Field")

_Field_alias = (Core.FieldName "alias")

_Field_name = (Core.FieldName "name")

_Field_arguments = (Core.FieldName "arguments")

_Field_directives = (Core.FieldName "directives")

_Field_selectionSet = (Core.FieldName "selectionSet")

data Alias = 
  AliasName Name |
  AliasColon 
  deriving (Eq, Ord, Read, Show)

_Alias = (Core.Name "hydra/langs/graphql/syntax.Alias")

_Alias_name = (Core.FieldName "name")

_Alias_colon = (Core.FieldName "colon")

newtype Arguments = 
  Arguments {
    unArguments :: [Argument]}
  deriving (Eq, Ord, Read, Show)

_Arguments = (Core.Name "hydra/langs/graphql/syntax.Arguments")

data Argument = 
  Argument {
    argumentName :: Name,
    argumentValue :: Value}
  deriving (Eq, Ord, Read, Show)

_Argument = (Core.Name "hydra/langs/graphql/syntax.Argument")

_Argument_name = (Core.FieldName "name")

_Argument_value = (Core.FieldName "value")

data FragmentSpread = 
  FragmentSpread {
    fragmentSpreadFragmentName :: FragmentName,
    fragmentSpreadDirectives :: (Maybe Directives)}
  deriving (Eq, Ord, Read, Show)

_FragmentSpread = (Core.Name "hydra/langs/graphql/syntax.FragmentSpread")

_FragmentSpread_fragmentName = (Core.FieldName "fragmentName")

_FragmentSpread_directives = (Core.FieldName "directives")

data InlineFragment = 
  InlineFragment {
    inlineFragmentTypeCondition :: (Maybe TypeCondition),
    inlineFragmentDirectives :: (Maybe Directives),
    inlineFragmentSelectionSet :: SelectionSet}
  deriving (Eq, Ord, Read, Show)

_InlineFragment = (Core.Name "hydra/langs/graphql/syntax.InlineFragment")

_InlineFragment_typeCondition = (Core.FieldName "typeCondition")

_InlineFragment_directives = (Core.FieldName "directives")

_InlineFragment_selectionSet = (Core.FieldName "selectionSet")

data FragmentDefinition = 
  FragmentDefinition {
    fragmentDefinitionFragmentName :: FragmentName,
    fragmentDefinitionTypeCondition :: TypeCondition,
    fragmentDefinitionDirectives :: (Maybe Directives),
    fragmentDefinitionSelectionSet :: SelectionSet}
  deriving (Eq, Ord, Read, Show)

_FragmentDefinition = (Core.Name "hydra/langs/graphql/syntax.FragmentDefinition")

_FragmentDefinition_fragmentName = (Core.FieldName "fragmentName")

_FragmentDefinition_typeCondition = (Core.FieldName "typeCondition")

_FragmentDefinition_directives = (Core.FieldName "directives")

_FragmentDefinition_selectionSet = (Core.FieldName "selectionSet")

newtype FragmentName = 
  FragmentName {
    unFragmentName :: Name}
  deriving (Eq, Ord, Read, Show)

_FragmentName = (Core.Name "hydra/langs/graphql/syntax.FragmentName")

data TypeCondition = 
  TypeConditionOn  |
  TypeConditionNamedType NamedType
  deriving (Eq, Ord, Read, Show)

_TypeCondition = (Core.Name "hydra/langs/graphql/syntax.TypeCondition")

_TypeCondition_on = (Core.FieldName "on")

_TypeCondition_namedType = (Core.FieldName "namedType")

data Value = 
  ValueVariable Variable |
  ValueInt IntValue |
  ValueFloat FloatValue |
  ValueString StringValue |
  ValueBoolean BooleanValue |
  ValueNull NullValue |
  ValueEnum EnumValue |
  ValueList ListValue |
  ValueObject ObjectValue
  deriving (Eq, Ord, Read, Show)

_Value = (Core.Name "hydra/langs/graphql/syntax.Value")

_Value_variable = (Core.FieldName "variable")

_Value_int = (Core.FieldName "int")

_Value_float = (Core.FieldName "float")

_Value_string = (Core.FieldName "string")

_Value_boolean = (Core.FieldName "boolean")

_Value_null = (Core.FieldName "null")

_Value_enum = (Core.FieldName "enum")

_Value_list = (Core.FieldName "list")

_Value_object = (Core.FieldName "object")

data BooleanValue = 
  BooleanValueTrue  |
  BooleanValueFalse 
  deriving (Eq, Ord, Read, Show)

_BooleanValue = (Core.Name "hydra/langs/graphql/syntax.BooleanValue")

_BooleanValue_true = (Core.FieldName "true")

_BooleanValue_false = (Core.FieldName "false")

data NullValue = 
  NullValue {}
  deriving (Eq, Ord, Read, Show)

_NullValue = (Core.Name "hydra/langs/graphql/syntax.NullValue")

newtype EnumValue = 
  EnumValue {
    unEnumValue :: Name}
  deriving (Eq, Ord, Read, Show)

_EnumValue = (Core.Name "hydra/langs/graphql/syntax.EnumValue")

data ListValue = 
  ListValueSequence ListValue_Sequence |
  ListValueSequence2 [Value]
  deriving (Eq, Ord, Read, Show)

_ListValue = (Core.Name "hydra/langs/graphql/syntax.ListValue")

_ListValue_sequence = (Core.FieldName "sequence")

_ListValue_sequence2 = (Core.FieldName "sequence2")

data ListValue_Sequence = 
  ListValue_Sequence {}
  deriving (Eq, Ord, Read, Show)

_ListValue_Sequence = (Core.Name "hydra/langs/graphql/syntax.ListValue.Sequence")

data ObjectValue = 
  ObjectValueSequence ObjectValue_Sequence |
  ObjectValueSequence2 [ObjectField]
  deriving (Eq, Ord, Read, Show)

_ObjectValue = (Core.Name "hydra/langs/graphql/syntax.ObjectValue")

_ObjectValue_sequence = (Core.FieldName "sequence")

_ObjectValue_sequence2 = (Core.FieldName "sequence2")

data ObjectValue_Sequence = 
  ObjectValue_Sequence {}
  deriving (Eq, Ord, Read, Show)

_ObjectValue_Sequence = (Core.Name "hydra/langs/graphql/syntax.ObjectValue.Sequence")

data ObjectField = 
  ObjectField {
    objectFieldName :: Name,
    objectFieldValue :: Value}
  deriving (Eq, Ord, Read, Show)

_ObjectField = (Core.Name "hydra/langs/graphql/syntax.ObjectField")

_ObjectField_name = (Core.FieldName "name")

_ObjectField_value = (Core.FieldName "value")

data VariablesDefinition = 
  VariablesDefinition {
    variablesDefinitionVariable :: Variable,
    variablesDefinitionType :: Type,
    variablesDefinitionDefaultValue :: (Maybe DefaultValue),
    variablesDefinitionDirectives :: (Maybe Directives)}
  deriving (Eq, Ord, Read, Show)

_VariablesDefinition = (Core.Name "hydra/langs/graphql/syntax.VariablesDefinition")

_VariablesDefinition_variable = (Core.FieldName "variable")

_VariablesDefinition_type = (Core.FieldName "type")

_VariablesDefinition_defaultValue = (Core.FieldName "defaultValue")

_VariablesDefinition_directives = (Core.FieldName "directives")

newtype Variable = 
  Variable {
    unVariable :: Name}
  deriving (Eq, Ord, Read, Show)

_Variable = (Core.Name "hydra/langs/graphql/syntax.Variable")

newtype DefaultValue = 
  DefaultValue {
    unDefaultValue :: Value}
  deriving (Eq, Ord, Read, Show)

_DefaultValue = (Core.Name "hydra/langs/graphql/syntax.DefaultValue")

data Type = 
  TypeNamed NamedType |
  TypeList ListType |
  TypeNonNull NonNullType
  deriving (Eq, Ord, Read, Show)

_Type = (Core.Name "hydra/langs/graphql/syntax.Type")

_Type_named = (Core.FieldName "named")

_Type_list = (Core.FieldName "list")

_Type_nonNull = (Core.FieldName "nonNull")

newtype NamedType = 
  NamedType {
    unNamedType :: Name}
  deriving (Eq, Ord, Read, Show)

_NamedType = (Core.Name "hydra/langs/graphql/syntax.NamedType")

newtype ListType = 
  ListType {
    unListType :: Type}
  deriving (Eq, Ord, Read, Show)

_ListType = (Core.Name "hydra/langs/graphql/syntax.ListType")

data NonNullType = 
  NonNullTypeNamed NamedType |
  NonNullTypeList ListType
  deriving (Eq, Ord, Read, Show)

_NonNullType = (Core.Name "hydra/langs/graphql/syntax.NonNullType")

_NonNullType_named = (Core.FieldName "named")

_NonNullType_list = (Core.FieldName "list")

newtype Directives = 
  Directives {
    unDirectives :: [Directive]}
  deriving (Eq, Ord, Read, Show)

_Directives = (Core.Name "hydra/langs/graphql/syntax.Directives")

data Directive = 
  Directive {
    directiveName :: Name,
    directiveArguments :: (Maybe Arguments)}
  deriving (Eq, Ord, Read, Show)

_Directive = (Core.Name "hydra/langs/graphql/syntax.Directive")

_Directive_name = (Core.FieldName "name")

_Directive_arguments = (Core.FieldName "arguments")

newtype TypeSystemDocment = 
  TypeSystemDocment {
    unTypeSystemDocment :: [TypeSystemDefinition]}
  deriving (Eq, Ord, Read, Show)

_TypeSystemDocment = (Core.Name "hydra/langs/graphql/syntax.TypeSystemDocment")

data TypeSystemDefinition = 
  TypeSystemDefinitionSchema SchemaDefinition |
  TypeSystemDefinitionType TypeDefinition |
  TypeSystemDefinitionDirective DirectiveDefinition
  deriving (Eq, Ord, Read, Show)

_TypeSystemDefinition = (Core.Name "hydra/langs/graphql/syntax.TypeSystemDefinition")

_TypeSystemDefinition_schema = (Core.FieldName "schema")

_TypeSystemDefinition_type = (Core.FieldName "type")

_TypeSystemDefinition_directive = (Core.FieldName "directive")

newtype TypeSystemExtensionDocument = 
  TypeSystemExtensionDocument {
    unTypeSystemExtensionDocument :: [TypeSystemDefinitionOrExtension]}
  deriving (Eq, Ord, Read, Show)

_TypeSystemExtensionDocument = (Core.Name "hydra/langs/graphql/syntax.TypeSystemExtensionDocument")

data TypeSystemDefinitionOrExtension = 
  TypeSystemDefinitionOrExtensionDefinition TypeSystemDefinition |
  TypeSystemDefinitionOrExtensionExtension TypeSystemExtension
  deriving (Eq, Ord, Read, Show)

_TypeSystemDefinitionOrExtension = (Core.Name "hydra/langs/graphql/syntax.TypeSystemDefinitionOrExtension")

_TypeSystemDefinitionOrExtension_definition = (Core.FieldName "definition")

_TypeSystemDefinitionOrExtension_extension = (Core.FieldName "extension")

data TypeSystemExtension = 
  TypeSystemExtensionSchema SchemaExtension |
  TypeSystemExtensionType TypeExtension
  deriving (Eq, Ord, Read, Show)

_TypeSystemExtension = (Core.Name "hydra/langs/graphql/syntax.TypeSystemExtension")

_TypeSystemExtension_schema = (Core.FieldName "schema")

_TypeSystemExtension_type = (Core.FieldName "type")

data SchemaDefinition = 
  SchemaDefinition {
    schemaDefinitionDescription :: (Maybe Description),
    schemaDefinitionDirectives :: (Maybe Directives),
    schemaDefinitionRootOperationTypeDefinition :: RootOperationTypeDefinition}
  deriving (Eq, Ord, Read, Show)

_SchemaDefinition = (Core.Name "hydra/langs/graphql/syntax.SchemaDefinition")

_SchemaDefinition_description = (Core.FieldName "description")

_SchemaDefinition_directives = (Core.FieldName "directives")

_SchemaDefinition_rootOperationTypeDefinition = (Core.FieldName "rootOperationTypeDefinition")

data SchemaExtension = 
  SchemaExtensionSequence SchemaExtension_Sequence |
  SchemaExtensionSequence2 Directives
  deriving (Eq, Ord, Read, Show)

_SchemaExtension = (Core.Name "hydra/langs/graphql/syntax.SchemaExtension")

_SchemaExtension_sequence = (Core.FieldName "sequence")

_SchemaExtension_sequence2 = (Core.FieldName "sequence2")

data SchemaExtension_Sequence = 
  SchemaExtension_Sequence {
    schemaExtension_SequenceDirectives :: (Maybe Directives),
    schemaExtension_SequenceRootOperationTypeDefinition :: RootOperationTypeDefinition}
  deriving (Eq, Ord, Read, Show)

_SchemaExtension_Sequence = (Core.Name "hydra/langs/graphql/syntax.SchemaExtension.Sequence")

_SchemaExtension_Sequence_directives = (Core.FieldName "directives")

_SchemaExtension_Sequence_rootOperationTypeDefinition = (Core.FieldName "rootOperationTypeDefinition")

data RootOperationTypeDefinition = 
  RootOperationTypeDefinition {
    rootOperationTypeDefinitionOperationType :: OperationType,
    rootOperationTypeDefinitionNamedType :: NamedType}
  deriving (Eq, Ord, Read, Show)

_RootOperationTypeDefinition = (Core.Name "hydra/langs/graphql/syntax.RootOperationTypeDefinition")

_RootOperationTypeDefinition_operationType = (Core.FieldName "operationType")

_RootOperationTypeDefinition_namedType = (Core.FieldName "namedType")

newtype Description = 
  Description {
    unDescription :: StringValue}
  deriving (Eq, Ord, Read, Show)

_Description = (Core.Name "hydra/langs/graphql/syntax.Description")

data TypeDefinition = 
  TypeDefinitionScalar ScalarTypeDefinition |
  TypeDefinitionObject ObjectTypeDefinition |
  TypeDefinitionInterface InterfaceTypeDefinition |
  TypeDefinitionUnion UnionTypeDefinition |
  TypeDefinitionEnum EnumTypeDefinition |
  TypeDefinitionInputObject InputObjectTypeDefinition
  deriving (Eq, Ord, Read, Show)

_TypeDefinition = (Core.Name "hydra/langs/graphql/syntax.TypeDefinition")

_TypeDefinition_scalar = (Core.FieldName "scalar")

_TypeDefinition_object = (Core.FieldName "object")

_TypeDefinition_interface = (Core.FieldName "interface")

_TypeDefinition_union = (Core.FieldName "union")

_TypeDefinition_enum = (Core.FieldName "enum")

_TypeDefinition_inputObject = (Core.FieldName "inputObject")

data TypeExtension = 
  TypeExtensionScalar ScalarTypeExtension |
  TypeExtensionObject ObjectTypeExtension |
  TypeExtensionInterface InterfaceTypeExtension |
  TypeExtensionUnion UnionTypeExtension |
  TypeExtensionEnum EnumTypeExtension |
  TypeExtensionInputObject InputObjectTypeExtension
  deriving (Eq, Ord, Read, Show)

_TypeExtension = (Core.Name "hydra/langs/graphql/syntax.TypeExtension")

_TypeExtension_scalar = (Core.FieldName "scalar")

_TypeExtension_object = (Core.FieldName "object")

_TypeExtension_interface = (Core.FieldName "interface")

_TypeExtension_union = (Core.FieldName "union")

_TypeExtension_enum = (Core.FieldName "enum")

_TypeExtension_inputObject = (Core.FieldName "inputObject")

data ScalarTypeDefinition = 
  ScalarTypeDefinition {
    scalarTypeDefinitionDescription :: (Maybe Description),
    scalarTypeDefinitionName :: Name,
    scalarTypeDefinitionDirectives :: (Maybe Directives)}
  deriving (Eq, Ord, Read, Show)

_ScalarTypeDefinition = (Core.Name "hydra/langs/graphql/syntax.ScalarTypeDefinition")

_ScalarTypeDefinition_description = (Core.FieldName "description")

_ScalarTypeDefinition_name = (Core.FieldName "name")

_ScalarTypeDefinition_directives = (Core.FieldName "directives")

data ScalarTypeExtension = 
  ScalarTypeExtension {
    scalarTypeExtensionName :: Name,
    scalarTypeExtensionDirectives :: Directives}
  deriving (Eq, Ord, Read, Show)

_ScalarTypeExtension = (Core.Name "hydra/langs/graphql/syntax.ScalarTypeExtension")

_ScalarTypeExtension_name = (Core.FieldName "name")

_ScalarTypeExtension_directives = (Core.FieldName "directives")

data ObjectTypeDefinition = 
  ObjectTypeDefinition {
    objectTypeDefinitionDescription :: (Maybe Description),
    objectTypeDefinitionName :: Name,
    objectTypeDefinitionImplementsInterfaces :: (Maybe ImplementsInterfaces),
    objectTypeDefinitionDirectives :: (Maybe Directives),
    objectTypeDefinitionFieldsDefinition :: (Maybe FieldsDefinition)}
  deriving (Eq, Ord, Read, Show)

_ObjectTypeDefinition = (Core.Name "hydra/langs/graphql/syntax.ObjectTypeDefinition")

_ObjectTypeDefinition_description = (Core.FieldName "description")

_ObjectTypeDefinition_name = (Core.FieldName "name")

_ObjectTypeDefinition_implementsInterfaces = (Core.FieldName "implementsInterfaces")

_ObjectTypeDefinition_directives = (Core.FieldName "directives")

_ObjectTypeDefinition_fieldsDefinition = (Core.FieldName "fieldsDefinition")

data ObjectTypeExtension = 
  ObjectTypeExtensionSequence ObjectTypeExtension_Sequence |
  ObjectTypeExtensionSequence2 ObjectTypeExtension_Sequence2 |
  ObjectTypeExtensionSequence3 ObjectTypeExtension_Sequence3
  deriving (Eq, Ord, Read, Show)

_ObjectTypeExtension = (Core.Name "hydra/langs/graphql/syntax.ObjectTypeExtension")

_ObjectTypeExtension_sequence = (Core.FieldName "sequence")

_ObjectTypeExtension_sequence2 = (Core.FieldName "sequence2")

_ObjectTypeExtension_sequence3 = (Core.FieldName "sequence3")

data ObjectTypeExtension_Sequence = 
  ObjectTypeExtension_Sequence {
    objectTypeExtension_SequenceName :: Name,
    objectTypeExtension_SequenceImplementsInterfaces :: (Maybe ImplementsInterfaces),
    objectTypeExtension_SequenceDirectives :: (Maybe Directives),
    objectTypeExtension_SequenceFieldsDefinition :: FieldsDefinition}
  deriving (Eq, Ord, Read, Show)

_ObjectTypeExtension_Sequence = (Core.Name "hydra/langs/graphql/syntax.ObjectTypeExtension.Sequence")

_ObjectTypeExtension_Sequence_name = (Core.FieldName "name")

_ObjectTypeExtension_Sequence_implementsInterfaces = (Core.FieldName "implementsInterfaces")

_ObjectTypeExtension_Sequence_directives = (Core.FieldName "directives")

_ObjectTypeExtension_Sequence_fieldsDefinition = (Core.FieldName "fieldsDefinition")

data ObjectTypeExtension_Sequence2 = 
  ObjectTypeExtension_Sequence2 {
    objectTypeExtension_Sequence2Name :: Name,
    objectTypeExtension_Sequence2ImplementsInterfaces :: (Maybe ImplementsInterfaces),
    objectTypeExtension_Sequence2Directives :: (Maybe Directives)}
  deriving (Eq, Ord, Read, Show)

_ObjectTypeExtension_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.ObjectTypeExtension.Sequence2")

_ObjectTypeExtension_Sequence2_name = (Core.FieldName "name")

_ObjectTypeExtension_Sequence2_implementsInterfaces = (Core.FieldName "implementsInterfaces")

_ObjectTypeExtension_Sequence2_directives = (Core.FieldName "directives")

data ObjectTypeExtension_Sequence3 = 
  ObjectTypeExtension_Sequence3 {
    objectTypeExtension_Sequence3Name :: Name,
    objectTypeExtension_Sequence3ImplementsInterfaces :: ImplementsInterfaces}
  deriving (Eq, Ord, Read, Show)

_ObjectTypeExtension_Sequence3 = (Core.Name "hydra/langs/graphql/syntax.ObjectTypeExtension.Sequence3")

_ObjectTypeExtension_Sequence3_name = (Core.FieldName "name")

_ObjectTypeExtension_Sequence3_implementsInterfaces = (Core.FieldName "implementsInterfaces")

data ImplementsInterfaces = 
  ImplementsInterfacesSequence ImplementsInterfaces_Sequence |
  ImplementsInterfacesSequence2 ImplementsInterfaces_Sequence2
  deriving (Eq, Ord, Read, Show)

_ImplementsInterfaces = (Core.Name "hydra/langs/graphql/syntax.ImplementsInterfaces")

_ImplementsInterfaces_sequence = (Core.FieldName "sequence")

_ImplementsInterfaces_sequence2 = (Core.FieldName "sequence2")

data ImplementsInterfaces_Sequence = 
  ImplementsInterfaces_Sequence {
    implementsInterfaces_SequenceImplementsInterfaces :: ImplementsInterfaces,
    implementsInterfaces_SequenceNamedType :: NamedType}
  deriving (Eq, Ord, Read, Show)

_ImplementsInterfaces_Sequence = (Core.Name "hydra/langs/graphql/syntax.ImplementsInterfaces.Sequence")

_ImplementsInterfaces_Sequence_implementsInterfaces = (Core.FieldName "implementsInterfaces")

_ImplementsInterfaces_Sequence_namedType = (Core.FieldName "namedType")

data ImplementsInterfaces_Sequence2 = 
  ImplementsInterfaces_Sequence2 {
    implementsInterfaces_Sequence2Amp :: (Maybe ()),
    implementsInterfaces_Sequence2NamedType :: NamedType}
  deriving (Eq, Ord, Read, Show)

_ImplementsInterfaces_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.ImplementsInterfaces.Sequence2")

_ImplementsInterfaces_Sequence2_amp = (Core.FieldName "amp")

_ImplementsInterfaces_Sequence2_namedType = (Core.FieldName "namedType")

newtype FieldsDefinition = 
  FieldsDefinition {
    unFieldsDefinition :: [FieldDefinition]}
  deriving (Eq, Ord, Read, Show)

_FieldsDefinition = (Core.Name "hydra/langs/graphql/syntax.FieldsDefinition")

data FieldDefinition = 
  FieldDefinition {
    fieldDefinitionDescription :: (Maybe Description),
    fieldDefinitionName :: Name,
    fieldDefinitionArgumentsDefinition :: (Maybe ArgumentsDefinition),
    fieldDefinitionType :: Type,
    fieldDefinitionDirectives :: (Maybe Directives)}
  deriving (Eq, Ord, Read, Show)

_FieldDefinition = (Core.Name "hydra/langs/graphql/syntax.FieldDefinition")

_FieldDefinition_description = (Core.FieldName "description")

_FieldDefinition_name = (Core.FieldName "name")

_FieldDefinition_argumentsDefinition = (Core.FieldName "argumentsDefinition")

_FieldDefinition_type = (Core.FieldName "type")

_FieldDefinition_directives = (Core.FieldName "directives")

newtype ArgumentsDefinition = 
  ArgumentsDefinition {
    unArgumentsDefinition :: [InputValueDefinition]}
  deriving (Eq, Ord, Read, Show)

_ArgumentsDefinition = (Core.Name "hydra/langs/graphql/syntax.ArgumentsDefinition")

data InputValueDefinition = 
  InputValueDefinition {
    inputValueDefinitionDescription :: (Maybe Description),
    inputValueDefinitionName :: Name,
    inputValueDefinitionType :: Type,
    inputValueDefinitionDefaultValue :: (Maybe DefaultValue),
    inputValueDefinitionDirectives :: (Maybe Directives)}
  deriving (Eq, Ord, Read, Show)

_InputValueDefinition = (Core.Name "hydra/langs/graphql/syntax.InputValueDefinition")

_InputValueDefinition_description = (Core.FieldName "description")

_InputValueDefinition_name = (Core.FieldName "name")

_InputValueDefinition_type = (Core.FieldName "type")

_InputValueDefinition_defaultValue = (Core.FieldName "defaultValue")

_InputValueDefinition_directives = (Core.FieldName "directives")

data InterfaceTypeDefinition = 
  InterfaceTypeDefinitionSequence InterfaceTypeDefinition_Sequence |
  InterfaceTypeDefinitionSequence2 InterfaceTypeDefinition_Sequence2
  deriving (Eq, Ord, Read, Show)

_InterfaceTypeDefinition = (Core.Name "hydra/langs/graphql/syntax.InterfaceTypeDefinition")

_InterfaceTypeDefinition_sequence = (Core.FieldName "sequence")

_InterfaceTypeDefinition_sequence2 = (Core.FieldName "sequence2")

data InterfaceTypeDefinition_Sequence = 
  InterfaceTypeDefinition_Sequence {
    interfaceTypeDefinition_SequenceDescription :: (Maybe Description),
    interfaceTypeDefinition_SequenceName :: Name,
    interfaceTypeDefinition_SequenceImplementsInterfaces :: (Maybe ImplementsInterfaces),
    interfaceTypeDefinition_SequenceDirectives :: (Maybe Directives),
    interfaceTypeDefinition_SequenceFieldsDefinition :: FieldsDefinition}
  deriving (Eq, Ord, Read, Show)

_InterfaceTypeDefinition_Sequence = (Core.Name "hydra/langs/graphql/syntax.InterfaceTypeDefinition.Sequence")

_InterfaceTypeDefinition_Sequence_description = (Core.FieldName "description")

_InterfaceTypeDefinition_Sequence_name = (Core.FieldName "name")

_InterfaceTypeDefinition_Sequence_implementsInterfaces = (Core.FieldName "implementsInterfaces")

_InterfaceTypeDefinition_Sequence_directives = (Core.FieldName "directives")

_InterfaceTypeDefinition_Sequence_fieldsDefinition = (Core.FieldName "fieldsDefinition")

data InterfaceTypeDefinition_Sequence2 = 
  InterfaceTypeDefinition_Sequence2 {
    interfaceTypeDefinition_Sequence2Description :: (Maybe Description),
    interfaceTypeDefinition_Sequence2Name :: Name,
    interfaceTypeDefinition_Sequence2ImplementsInterfaces :: ImplementsInterfaces,
    interfaceTypeDefinition_Sequence2Directives :: (Maybe Directives)}
  deriving (Eq, Ord, Read, Show)

_InterfaceTypeDefinition_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.InterfaceTypeDefinition.Sequence2")

_InterfaceTypeDefinition_Sequence2_description = (Core.FieldName "description")

_InterfaceTypeDefinition_Sequence2_name = (Core.FieldName "name")

_InterfaceTypeDefinition_Sequence2_implementsInterfaces = (Core.FieldName "implementsInterfaces")

_InterfaceTypeDefinition_Sequence2_directives = (Core.FieldName "directives")

data InterfaceTypeExtension = 
  InterfaceTypeExtensionSequence InterfaceTypeExtension_Sequence |
  InterfaceTypeExtensionSequence2 InterfaceTypeExtension_Sequence2 |
  InterfaceTypeExtensionSequence3 InterfaceTypeExtension_Sequence3
  deriving (Eq, Ord, Read, Show)

_InterfaceTypeExtension = (Core.Name "hydra/langs/graphql/syntax.InterfaceTypeExtension")

_InterfaceTypeExtension_sequence = (Core.FieldName "sequence")

_InterfaceTypeExtension_sequence2 = (Core.FieldName "sequence2")

_InterfaceTypeExtension_sequence3 = (Core.FieldName "sequence3")

data InterfaceTypeExtension_Sequence = 
  InterfaceTypeExtension_Sequence {
    interfaceTypeExtension_SequenceName :: Name,
    interfaceTypeExtension_SequenceImplementsInterfaces :: (Maybe ImplementsInterfaces),
    interfaceTypeExtension_SequenceDirectives :: (Maybe Directives),
    interfaceTypeExtension_SequenceFieldsDefinition :: FieldsDefinition}
  deriving (Eq, Ord, Read, Show)

_InterfaceTypeExtension_Sequence = (Core.Name "hydra/langs/graphql/syntax.InterfaceTypeExtension.Sequence")

_InterfaceTypeExtension_Sequence_name = (Core.FieldName "name")

_InterfaceTypeExtension_Sequence_implementsInterfaces = (Core.FieldName "implementsInterfaces")

_InterfaceTypeExtension_Sequence_directives = (Core.FieldName "directives")

_InterfaceTypeExtension_Sequence_fieldsDefinition = (Core.FieldName "fieldsDefinition")

data InterfaceTypeExtension_Sequence2 = 
  InterfaceTypeExtension_Sequence2 {
    interfaceTypeExtension_Sequence2Name :: Name,
    interfaceTypeExtension_Sequence2ImplementsInterfaces :: (Maybe ImplementsInterfaces),
    interfaceTypeExtension_Sequence2Directives :: Directives}
  deriving (Eq, Ord, Read, Show)

_InterfaceTypeExtension_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.InterfaceTypeExtension.Sequence2")

_InterfaceTypeExtension_Sequence2_name = (Core.FieldName "name")

_InterfaceTypeExtension_Sequence2_implementsInterfaces = (Core.FieldName "implementsInterfaces")

_InterfaceTypeExtension_Sequence2_directives = (Core.FieldName "directives")

data InterfaceTypeExtension_Sequence3 = 
  InterfaceTypeExtension_Sequence3 {
    interfaceTypeExtension_Sequence3Name :: Name,
    interfaceTypeExtension_Sequence3ImplementsInterfaces :: ImplementsInterfaces}
  deriving (Eq, Ord, Read, Show)

_InterfaceTypeExtension_Sequence3 = (Core.Name "hydra/langs/graphql/syntax.InterfaceTypeExtension.Sequence3")

_InterfaceTypeExtension_Sequence3_name = (Core.FieldName "name")

_InterfaceTypeExtension_Sequence3_implementsInterfaces = (Core.FieldName "implementsInterfaces")

data UnionTypeDefinition = 
  UnionTypeDefinition {
    unionTypeDefinitionDescription :: (Maybe Description),
    unionTypeDefinitionName :: Name,
    unionTypeDefinitionDirectives :: (Maybe Directives),
    unionTypeDefinitionUnionMemberTypes :: (Maybe UnionMemberTypes)}
  deriving (Eq, Ord, Read, Show)

_UnionTypeDefinition = (Core.Name "hydra/langs/graphql/syntax.UnionTypeDefinition")

_UnionTypeDefinition_description = (Core.FieldName "description")

_UnionTypeDefinition_name = (Core.FieldName "name")

_UnionTypeDefinition_directives = (Core.FieldName "directives")

_UnionTypeDefinition_unionMemberTypes = (Core.FieldName "unionMemberTypes")

data UnionMemberTypes = 
  UnionMemberTypesSequence UnionMemberTypes_Sequence |
  UnionMemberTypesSequence2 UnionMemberTypes_Sequence2
  deriving (Eq, Ord, Read, Show)

_UnionMemberTypes = (Core.Name "hydra/langs/graphql/syntax.UnionMemberTypes")

_UnionMemberTypes_sequence = (Core.FieldName "sequence")

_UnionMemberTypes_sequence2 = (Core.FieldName "sequence2")

data UnionMemberTypes_Sequence = 
  UnionMemberTypes_Sequence {
    unionMemberTypes_SequenceUnionMemberTypes :: UnionMemberTypes,
    unionMemberTypes_SequenceNamedType :: NamedType}
  deriving (Eq, Ord, Read, Show)

_UnionMemberTypes_Sequence = (Core.Name "hydra/langs/graphql/syntax.UnionMemberTypes.Sequence")

_UnionMemberTypes_Sequence_unionMemberTypes = (Core.FieldName "unionMemberTypes")

_UnionMemberTypes_Sequence_namedType = (Core.FieldName "namedType")

data UnionMemberTypes_Sequence2 = 
  UnionMemberTypes_Sequence2 {
    unionMemberTypes_Sequence2Or :: (Maybe ()),
    unionMemberTypes_Sequence2NamedType :: NamedType}
  deriving (Eq, Ord, Read, Show)

_UnionMemberTypes_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.UnionMemberTypes.Sequence2")

_UnionMemberTypes_Sequence2_or = (Core.FieldName "or")

_UnionMemberTypes_Sequence2_namedType = (Core.FieldName "namedType")

data UnionTypeExtension = 
  UnionTypeExtensionSequence UnionTypeExtension_Sequence |
  UnionTypeExtensionSequence2 UnionTypeExtension_Sequence2
  deriving (Eq, Ord, Read, Show)

_UnionTypeExtension = (Core.Name "hydra/langs/graphql/syntax.UnionTypeExtension")

_UnionTypeExtension_sequence = (Core.FieldName "sequence")

_UnionTypeExtension_sequence2 = (Core.FieldName "sequence2")

data UnionTypeExtension_Sequence = 
  UnionTypeExtension_Sequence {
    unionTypeExtension_SequenceName :: Name,
    unionTypeExtension_SequenceDirectives :: (Maybe Directives),
    unionTypeExtension_SequenceUnionMemberTypes :: UnionMemberTypes}
  deriving (Eq, Ord, Read, Show)

_UnionTypeExtension_Sequence = (Core.Name "hydra/langs/graphql/syntax.UnionTypeExtension.Sequence")

_UnionTypeExtension_Sequence_name = (Core.FieldName "name")

_UnionTypeExtension_Sequence_directives = (Core.FieldName "directives")

_UnionTypeExtension_Sequence_unionMemberTypes = (Core.FieldName "unionMemberTypes")

data UnionTypeExtension_Sequence2 = 
  UnionTypeExtension_Sequence2 {
    unionTypeExtension_Sequence2Name :: Name,
    unionTypeExtension_Sequence2Directives :: Directives}
  deriving (Eq, Ord, Read, Show)

_UnionTypeExtension_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.UnionTypeExtension.Sequence2")

_UnionTypeExtension_Sequence2_name = (Core.FieldName "name")

_UnionTypeExtension_Sequence2_directives = (Core.FieldName "directives")

data EnumTypeDefinition = 
  EnumTypeDefinition {
    enumTypeDefinitionDescription :: (Maybe Description),
    enumTypeDefinitionName :: Name,
    enumTypeDefinitionDirectives :: (Maybe Directives),
    enumTypeDefinitionEnumValuesDefinition :: (Maybe EnumValuesDefinition)}
  deriving (Eq, Ord, Read, Show)

_EnumTypeDefinition = (Core.Name "hydra/langs/graphql/syntax.EnumTypeDefinition")

_EnumTypeDefinition_description = (Core.FieldName "description")

_EnumTypeDefinition_name = (Core.FieldName "name")

_EnumTypeDefinition_directives = (Core.FieldName "directives")

_EnumTypeDefinition_enumValuesDefinition = (Core.FieldName "enumValuesDefinition")

newtype EnumValuesDefinition = 
  EnumValuesDefinition {
    unEnumValuesDefinition :: [EnumValueDefinition]}
  deriving (Eq, Ord, Read, Show)

_EnumValuesDefinition = (Core.Name "hydra/langs/graphql/syntax.EnumValuesDefinition")

data EnumValueDefinition = 
  EnumValueDefinition {
    enumValueDefinitionDescription :: (Maybe Description),
    enumValueDefinitionEnumValue :: EnumValue,
    enumValueDefinitionDirectives :: (Maybe Directives)}
  deriving (Eq, Ord, Read, Show)

_EnumValueDefinition = (Core.Name "hydra/langs/graphql/syntax.EnumValueDefinition")

_EnumValueDefinition_description = (Core.FieldName "description")

_EnumValueDefinition_enumValue = (Core.FieldName "enumValue")

_EnumValueDefinition_directives = (Core.FieldName "directives")

data EnumTypeExtension = 
  EnumTypeExtensionSequence EnumTypeExtension_Sequence |
  EnumTypeExtensionSequence2 EnumTypeExtension_Sequence2
  deriving (Eq, Ord, Read, Show)

_EnumTypeExtension = (Core.Name "hydra/langs/graphql/syntax.EnumTypeExtension")

_EnumTypeExtension_sequence = (Core.FieldName "sequence")

_EnumTypeExtension_sequence2 = (Core.FieldName "sequence2")

data EnumTypeExtension_Sequence = 
  EnumTypeExtension_Sequence {
    enumTypeExtension_SequenceName :: Name,
    enumTypeExtension_SequenceDirectives :: (Maybe Directives),
    enumTypeExtension_SequenceEnumValuesDefinition :: EnumValuesDefinition}
  deriving (Eq, Ord, Read, Show)

_EnumTypeExtension_Sequence = (Core.Name "hydra/langs/graphql/syntax.EnumTypeExtension.Sequence")

_EnumTypeExtension_Sequence_name = (Core.FieldName "name")

_EnumTypeExtension_Sequence_directives = (Core.FieldName "directives")

_EnumTypeExtension_Sequence_enumValuesDefinition = (Core.FieldName "enumValuesDefinition")

data EnumTypeExtension_Sequence2 = 
  EnumTypeExtension_Sequence2 {
    enumTypeExtension_Sequence2Name :: Name,
    enumTypeExtension_Sequence2Directives :: Directives}
  deriving (Eq, Ord, Read, Show)

_EnumTypeExtension_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.EnumTypeExtension.Sequence2")

_EnumTypeExtension_Sequence2_name = (Core.FieldName "name")

_EnumTypeExtension_Sequence2_directives = (Core.FieldName "directives")

data InputObjectTypeDefinition = 
  InputObjectTypeDefinitionSequence InputObjectTypeDefinition_Sequence |
  InputObjectTypeDefinitionSequence2 InputObjectTypeDefinition_Sequence2
  deriving (Eq, Ord, Read, Show)

_InputObjectTypeDefinition = (Core.Name "hydra/langs/graphql/syntax.InputObjectTypeDefinition")

_InputObjectTypeDefinition_sequence = (Core.FieldName "sequence")

_InputObjectTypeDefinition_sequence2 = (Core.FieldName "sequence2")

data InputObjectTypeDefinition_Sequence = 
  InputObjectTypeDefinition_Sequence {
    inputObjectTypeDefinition_SequenceDescription :: (Maybe Description),
    inputObjectTypeDefinition_SequenceName :: Name,
    inputObjectTypeDefinition_SequenceDirectives :: (Maybe Directives),
    inputObjectTypeDefinition_SequenceInputFieldsDefinition :: InputFieldsDefinition}
  deriving (Eq, Ord, Read, Show)

_InputObjectTypeDefinition_Sequence = (Core.Name "hydra/langs/graphql/syntax.InputObjectTypeDefinition.Sequence")

_InputObjectTypeDefinition_Sequence_description = (Core.FieldName "description")

_InputObjectTypeDefinition_Sequence_name = (Core.FieldName "name")

_InputObjectTypeDefinition_Sequence_directives = (Core.FieldName "directives")

_InputObjectTypeDefinition_Sequence_inputFieldsDefinition = (Core.FieldName "inputFieldsDefinition")

data InputObjectTypeDefinition_Sequence2 = 
  InputObjectTypeDefinition_Sequence2 {
    inputObjectTypeDefinition_Sequence2Description :: (Maybe Description),
    inputObjectTypeDefinition_Sequence2Name :: Name,
    inputObjectTypeDefinition_Sequence2Directives :: (Maybe Directives)}
  deriving (Eq, Ord, Read, Show)

_InputObjectTypeDefinition_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.InputObjectTypeDefinition.Sequence2")

_InputObjectTypeDefinition_Sequence2_description = (Core.FieldName "description")

_InputObjectTypeDefinition_Sequence2_name = (Core.FieldName "name")

_InputObjectTypeDefinition_Sequence2_directives = (Core.FieldName "directives")

newtype InputFieldsDefinition = 
  InputFieldsDefinition {
    unInputFieldsDefinition :: [InputValueDefinition]}
  deriving (Eq, Ord, Read, Show)

_InputFieldsDefinition = (Core.Name "hydra/langs/graphql/syntax.InputFieldsDefinition")

data InputObjectTypeExtension = 
  InputObjectTypeExtensionSequence InputObjectTypeExtension_Sequence |
  InputObjectTypeExtensionSequence2 InputObjectTypeExtension_Sequence2
  deriving (Eq, Ord, Read, Show)

_InputObjectTypeExtension = (Core.Name "hydra/langs/graphql/syntax.InputObjectTypeExtension")

_InputObjectTypeExtension_sequence = (Core.FieldName "sequence")

_InputObjectTypeExtension_sequence2 = (Core.FieldName "sequence2")

data InputObjectTypeExtension_Sequence = 
  InputObjectTypeExtension_Sequence {
    inputObjectTypeExtension_SequenceName :: Name,
    inputObjectTypeExtension_SequenceDirectives :: (Maybe Directives),
    inputObjectTypeExtension_SequenceInputFieldsDefinition :: InputFieldsDefinition}
  deriving (Eq, Ord, Read, Show)

_InputObjectTypeExtension_Sequence = (Core.Name "hydra/langs/graphql/syntax.InputObjectTypeExtension.Sequence")

_InputObjectTypeExtension_Sequence_name = (Core.FieldName "name")

_InputObjectTypeExtension_Sequence_directives = (Core.FieldName "directives")

_InputObjectTypeExtension_Sequence_inputFieldsDefinition = (Core.FieldName "inputFieldsDefinition")

data InputObjectTypeExtension_Sequence2 = 
  InputObjectTypeExtension_Sequence2 {
    inputObjectTypeExtension_Sequence2Name :: Name,
    inputObjectTypeExtension_Sequence2Directives :: Directives}
  deriving (Eq, Ord, Read, Show)

_InputObjectTypeExtension_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.InputObjectTypeExtension.Sequence2")

_InputObjectTypeExtension_Sequence2_name = (Core.FieldName "name")

_InputObjectTypeExtension_Sequence2_directives = (Core.FieldName "directives")

data DirectiveDefinition = 
  DirectiveDefinition {
    directiveDefinitionDescription :: (Maybe Description),
    directiveDefinitionName :: Name,
    directiveDefinitionArgumentsDefinition :: (Maybe ArgumentsDefinition),
    directiveDefinitionRepeatable :: (Maybe ()),
    directiveDefinitionDirectiveLocations :: DirectiveLocations}
  deriving (Eq, Ord, Read, Show)

_DirectiveDefinition = (Core.Name "hydra/langs/graphql/syntax.DirectiveDefinition")

_DirectiveDefinition_description = (Core.FieldName "description")

_DirectiveDefinition_name = (Core.FieldName "name")

_DirectiveDefinition_argumentsDefinition = (Core.FieldName "argumentsDefinition")

_DirectiveDefinition_repeatable = (Core.FieldName "repeatable")

_DirectiveDefinition_directiveLocations = (Core.FieldName "directiveLocations")

data DirectiveLocations = 
  DirectiveLocationsSequence DirectiveLocations_Sequence |
  DirectiveLocationsSequence2 DirectiveLocations_Sequence2
  deriving (Eq, Ord, Read, Show)

_DirectiveLocations = (Core.Name "hydra/langs/graphql/syntax.DirectiveLocations")

_DirectiveLocations_sequence = (Core.FieldName "sequence")

_DirectiveLocations_sequence2 = (Core.FieldName "sequence2")

data DirectiveLocations_Sequence = 
  DirectiveLocations_Sequence {
    directiveLocations_SequenceDirectiveLocations :: DirectiveLocations,
    directiveLocations_SequenceDirectiveLocation :: DirectiveLocation}
  deriving (Eq, Ord, Read, Show)

_DirectiveLocations_Sequence = (Core.Name "hydra/langs/graphql/syntax.DirectiveLocations.Sequence")

_DirectiveLocations_Sequence_directiveLocations = (Core.FieldName "directiveLocations")

_DirectiveLocations_Sequence_directiveLocation = (Core.FieldName "directiveLocation")

data DirectiveLocations_Sequence2 = 
  DirectiveLocations_Sequence2 {
    directiveLocations_Sequence2Or :: (Maybe ()),
    directiveLocations_Sequence2DirectiveLocation :: DirectiveLocation}
  deriving (Eq, Ord, Read, Show)

_DirectiveLocations_Sequence2 = (Core.Name "hydra/langs/graphql/syntax.DirectiveLocations.Sequence2")

_DirectiveLocations_Sequence2_or = (Core.FieldName "or")

_DirectiveLocations_Sequence2_directiveLocation = (Core.FieldName "directiveLocation")

data DirectiveLocation = 
  DirectiveLocationExecutable ExecutableDirectiveLocation |
  DirectiveLocationTypeSystem TypeSystemDirectiveLocation
  deriving (Eq, Ord, Read, Show)

_DirectiveLocation = (Core.Name "hydra/langs/graphql/syntax.DirectiveLocation")

_DirectiveLocation_executable = (Core.FieldName "executable")

_DirectiveLocation_typeSystem = (Core.FieldName "typeSystem")

data ExecutableDirectiveLocation = 
  ExecutableDirectiveLocationQUERY  |
  ExecutableDirectiveLocationMUTATION  |
  ExecutableDirectiveLocationSUBSCRIPTION  |
  ExecutableDirectiveLocationFIELD  |
  ExecutableDirectiveLocationFRAGMENTLowbarDEFINITION  |
  ExecutableDirectiveLocationFRAGMENTLowbarSPREAD  |
  ExecutableDirectiveLocationINLINELowbarFRAGMENT  |
  ExecutableDirectiveLocationVARIABLELowbarDEFINITION 
  deriving (Eq, Ord, Read, Show)

_ExecutableDirectiveLocation = (Core.Name "hydra/langs/graphql/syntax.ExecutableDirectiveLocation")

_ExecutableDirectiveLocation_qUERY = (Core.FieldName "qUERY")

_ExecutableDirectiveLocation_mUTATION = (Core.FieldName "mUTATION")

_ExecutableDirectiveLocation_sUBSCRIPTION = (Core.FieldName "sUBSCRIPTION")

_ExecutableDirectiveLocation_fIELD = (Core.FieldName "fIELD")

_ExecutableDirectiveLocation_fRAGMENTLowbarDEFINITION = (Core.FieldName "fRAGMENTLowbarDEFINITION")

_ExecutableDirectiveLocation_fRAGMENTLowbarSPREAD = (Core.FieldName "fRAGMENTLowbarSPREAD")

_ExecutableDirectiveLocation_iNLINELowbarFRAGMENT = (Core.FieldName "iNLINELowbarFRAGMENT")

_ExecutableDirectiveLocation_vARIABLELowbarDEFINITION = (Core.FieldName "vARIABLELowbarDEFINITION")

data TypeSystemDirectiveLocation = 
  TypeSystemDirectiveLocationSCHEMA  |
  TypeSystemDirectiveLocationSCALAR  |
  TypeSystemDirectiveLocationOBJECT  |
  TypeSystemDirectiveLocationFIELDLowbarDEFINITION  |
  TypeSystemDirectiveLocationARGUMENTLowbarDEFINITION  |
  TypeSystemDirectiveLocationINTERFACE  |
  TypeSystemDirectiveLocationUNION  |
  TypeSystemDirectiveLocationENUM  |
  TypeSystemDirectiveLocationENUMLowbarVALUE  |
  TypeSystemDirectiveLocationINPUTLowbarOBJECT  |
  TypeSystemDirectiveLocationINPUTLowbarFIELDLowbarDEFINITION 
  deriving (Eq, Ord, Read, Show)

_TypeSystemDirectiveLocation = (Core.Name "hydra/langs/graphql/syntax.TypeSystemDirectiveLocation")

_TypeSystemDirectiveLocation_sCHEMA = (Core.FieldName "sCHEMA")

_TypeSystemDirectiveLocation_sCALAR = (Core.FieldName "sCALAR")

_TypeSystemDirectiveLocation_oBJECT = (Core.FieldName "oBJECT")

_TypeSystemDirectiveLocation_fIELDLowbarDEFINITION = (Core.FieldName "fIELDLowbarDEFINITION")

_TypeSystemDirectiveLocation_aRGUMENTLowbarDEFINITION = (Core.FieldName "aRGUMENTLowbarDEFINITION")

_TypeSystemDirectiveLocation_iNTERFACE = (Core.FieldName "iNTERFACE")

_TypeSystemDirectiveLocation_uNION = (Core.FieldName "uNION")

_TypeSystemDirectiveLocation_eNUM = (Core.FieldName "eNUM")

_TypeSystemDirectiveLocation_eNUMLowbarVALUE = (Core.FieldName "eNUMLowbarVALUE")

_TypeSystemDirectiveLocation_iNPUTLowbarOBJECT = (Core.FieldName "iNPUTLowbarOBJECT")

_TypeSystemDirectiveLocation_iNPUTLowbarFIELDLowbarDEFINITION = (Core.FieldName "iNPUTLowbarFIELDLowbarDEFINITION")
