{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Langs.Graphql.Syntax where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Grammars
import Hydra.Tools.GrammarToModule
import qualified Hydra.Grammar as G


and_ = terminal "&"
at_ = terminal "@"
bang_ = terminal "!"
colon_ = terminal ":"
directive_ = terminal "directive"
dollar_ = terminal "$"
ellipsis_ = terminal "..."
enum_ = terminal "enum"
equal_ = terminal "="
extend_ = terminal "extend"
false_ = terminal "false"
implements_ = terminal "implements"
input_ = terminal "input"
interface_ = terminal "interface"
lbracket_ = terminal "["
lcurly_ = terminal "{"
lparen_ = terminal "("
null_ = terminal "null"
on_ = terminal "on"
or_ = terminal "or"
rbracket_ = terminal "]"
rcurly_ = terminal "}"
repeatable_ = terminal "repeatable"
rparen_ = terminal ")"
scalar_ = terminal "scalar"
schema_ = terminal "schema"
true_ = terminal "true"
type_ = terminal "type"
union_ = terminal "union"

descriptionOpt = opt"Description"
directivesConst = "Directives" -- Directives_[Const]
directivesConstOpt = opt"Directives" -- Directives_[Const]opt

graphqlSyntaxModule :: Module
graphqlSyntaxModule = grammarToModule ns graphqlGrammar $
    Just ("A GraphQL model. Based on the (extended) BNF at:\n" ++
      "  https://spec.graphql.org/draft/#sec-Appendix-Grammar-Summary")
  where
    ns = Namespace "hydra/langs/graphql/syntax"

graphqlGrammar :: G.Grammar
graphqlGrammar = G.Grammar $ tokenDefinitions ++ documentDefinitions

tokenDefinitions :: [G.Production]
tokenDefinitions = [
  define "Name"        [regex "[A-Za-z][A-Za-z0-9]*"],
  define "IntValue"    [regex "-?(0|[1-9][0-9]*)"],
  define "FloatValue"  [regex "-?(0|[1-9][0-9]*)([.][0-9]+|[eE][+-]?[0-9]+)"],
  define "StringValue" [regex "[\"].*[\"]"]] -- TODO: the actual expression includes Unicode escape sequences

documentDefinitions :: [G.Production]
documentDefinitions = [
  define "Document" [
    star"Definition"],

  define "Definition" [
    "executable">: "ExecutableDefinition",
    "typeSystem">: "TypeSystemDefinitionOrExtension"],

  define "ExecutableDocument" [
    star"ExecutableDefinition"],

  define "ExecutableDefinition" [
    "operation">: "OperationDefinition",
    "fragment">: "FragmentDefinition"],

  define "OperationDefinition" [
    list["OperationType", opt"Name", opt"VariablesDefinition", opt"Directives", "SelectionSet"],
    "SelectionSet"],

  define "OperationType" [
    terminal "query",
    terminal "mutation",
    terminal "subscription"],

  define "SelectionSet" [
    list[lcurly_, star"Selection", rcurly_]],

  define "Selection" [
    "Field",
    "FragmentSpread",
    "InlineFragment"],

  define "Field" [
    list[opt"Alias", "Name", opt"Arguments", opt"Directives", opt"SelectionSet"]],

  define "Alias" [
    "Name", colon_],

  define "Arguments"{- [Const] -} [
    list[lparen_, star"Argument"{- [?Const] -}, rparen_]],

  define "Argument"{- [Const] -} [
    list["Name", colon_, "Value"{- [?Const] -}]],

  define "FragmentSpread" [
    list[ellipsis_, "FragmentName", opt"Directives"]],

  define "InlineFragment" [
    list[ellipsis_, opt"TypeCondition", opt"Directives", "SelectionSet"]],

  define "FragmentDefinition" [
    list[terminal "fragment", "FragmentName", "TypeCondition", opt"Directives", "SelectionSet"]],

  define "FragmentName" [
    "Name" {- but not on_ -}],

  define "TypeCondition" [
    on_, "NamedType"],

  define "Value"{- [Const] -} [
    {- [if not Const] -} "Variable",
    "int">: "IntValue",
    "float">: "FloatValue",
    "string">: "StringValue",
    "boolean">: "BooleanValue",
    "null">: "NullValue",
    "enum">: "EnumValue",
    "list">: "ListValue"{- [?Const] -},
    "object">: "ObjectValue"{- [?Const] -}],

  define "BooleanValue" [
    true_,
    false_],

  define "NullValue" [
    null_],

  define "EnumValue" [
    list["Name" {- but not true_ or false_ or null_ -}]],

  define "ListValue"{- [Const] -} [
    list[lbracket_, rbracket_],
    list[lbracket_, star"Value"{- [?Const] -}]],

  define "ObjectValue"{- [Const] -} [
    list[lcurly_, rcurly_],
    list[star"ObjectField"{- [?Const] -}]],

  define "ObjectField"{- [Const] -} [
    list["Name", colon_, "Value"{- [?Const] -}]],

  define "VariablesDefinition" [
    list["Variable", colon_, "Type", opt"DefaultValue", directivesConstOpt]],

  define "Variable" [
    "Name"],

  define "DefaultValue" [
    list[equal_, "Value"{- [Const] -}]],

  define "Type" [
    "named">: "NamedType",
    "list">: "ListType",
    "nonNull">: "NonNullType"],

  define "NamedType" [
    "Name"],

  define "ListType" [
    list[lbracket_, "Type", rbracket_]],

  define "NonNullType" [
    "named">: list["NamedType", bang_],
    "list">: list["ListType", bang_]],

  define "Directives"{- [Const] -} [
    star("Directive"{- [?Const] -})],

  define "Directive"{- [Const] -} [
    list[at_, "Name", opt("Arguments"{- [?Const] -})]],

  define "TypeSystemDocment" [
    star"TypeSystemDefinition"],

  define "TypeSystemDefinition" [
    "schema">: "SchemaDefinition",
    "type">: "TypeDefinition",
    "directive">: "DirectiveDefinition"],

  define "TypeSystemExtensionDocument" [
    star"TypeSystemDefinitionOrExtension"],

  define "TypeSystemDefinitionOrExtension" [
    "definition">: "TypeSystemDefinition",
    "extension">: "TypeSystemExtension"],

  define "TypeSystemExtension" [
    "schema">: "SchemaExtension",
    "type">: "TypeExtension"],

  define "SchemaDefinition" [
    list[descriptionOpt, schema_, directivesConstOpt, lcurly_, "RootOperationTypeDefinition", rcurly_]],

  define "SchemaExtension" [
    list[extend_, schema_, directivesConstOpt, lcurly_, "RootOperationTypeDefinition", rcurly_],
    list[extend_, schema_, directivesConst {- [lookahead != lcurly_] -}]],

  define "RootOperationTypeDefinition" [
    list["OperationType", colon_, "NamedType"]],

  define "Description" [
    "StringValue"],

  define "TypeDefinition" [
    "scalar">: "ScalarTypeDefinition",
    "object">: "ObjectTypeDefinition",
    "interface">: "InterfaceTypeDefinition",
    "union">: "UnionTypeDefinition",
    "enum">: "EnumTypeDefinition",
    "inputObject">: "InputObjectTypeDefinition"],

  define "TypeExtension" [
    "scalar">: "ScalarTypeExtension",
    "object">: "ObjectTypeExtension",
    "interface">: "InterfaceTypeExtension",
    "union">: "UnionTypeExtension",
    "enum">: "EnumTypeExtension",
    "inputObject">: "InputObjectTypeExtension"],

  define "ScalarTypeDefinition" [
    list[descriptionOpt, scalar_, "Name", directivesConstOpt ]],

  define "ScalarTypeExtension" [
    list[extend_, scalar_, "Name", directivesConst]],

  define "ObjectTypeDefinition" [
    list[descriptionOpt, type_, "Name", opt"ImplementsInterfaces", directivesConstOpt, opt("FieldsDefinition") {- [lookahead != lcurly_] -}]],

  define "ObjectTypeExtension" [
    list[extend_, type_, "Name", opt"ImplementsInterfaces", directivesConstOpt, "FieldsDefinition"],
    list[extend_, type_, "Name", opt"ImplementsInterfaces", directivesConstOpt {- [lookahead != lcurly_] -}],
    list[extend_, type_, "Name", "ImplementsInterfaces" {- [lookahead != lcurly_] -}]],

  define "ImplementsInterfaces" [
    list["ImplementsInterfaces", and_, "NamedType"],
    list[implements_, opt(and_), "NamedType"]],

  define "FieldsDefinition" [
    list[lcurly_, star"FieldDefinition", rcurly_]],

  define "FieldDefinition" [
    list[descriptionOpt, "Name", opt"ArgumentsDefinition", colon_, "Type", directivesConstOpt]],

  define "ArgumentsDefinition" [
    list[lparen_, star"InputValueDefinition", rparen_]],

  define "InputValueDefinition" [
    list[descriptionOpt, "Name", colon_, "Type", opt"DefaultValue", directivesConstOpt]],

  define "InterfaceTypeDefinition" [
    list[descriptionOpt, interface_, "Name", opt"ImplementsInterfaces", directivesConstOpt, "FieldsDefinition"],
    list[descriptionOpt, interface_, "Name", "ImplementsInterfaces", directivesConstOpt {- [lookahead != lcurly_] -}]],

  define "InterfaceTypeExtension" [
    list[extend_, interface_, "Name", opt"ImplementsInterfaces", directivesConstOpt, "FieldsDefinition"],
    list[extend_, interface_, "Name", opt"ImplementsInterfaces", directivesConst {- [lookahead != lcurly_] -}],
    list[extend_, interface_, "Name", "ImplementsInterfaces" {- [lookahead != lcurly_] -}]],

  define "UnionTypeDefinition" [
    list[descriptionOpt, union_, "Name", directivesConstOpt, opt"UnionMemberTypes"]],

  define "UnionMemberTypes" [
    list["UnionMemberTypes", or_, "NamedType"],
    list[opt(or_), "NamedType"]],

  define "UnionTypeExtension" [
    list[extend_, union_, "Name", directivesConstOpt, "UnionMemberTypes"],
    list[extend_, union_, "Name", directivesConst]],

  define "EnumTypeDefinition" [
    list[descriptionOpt, enum_, "Name", directivesConstOpt, opt("EnumValuesDefinition")  {- [lookahead != lcurly_] -}]],

  define "EnumValuesDefinition" [
    list[lcurly_, star"EnumValueDefinition", rcurly_]],

  define "EnumValueDefinition" [
    list[descriptionOpt, "EnumValue", directivesConstOpt]],

  define "EnumTypeExtension" [
    list[extend_, enum_, "Name", directivesConstOpt, "EnumValuesDefinition"],
    list[extend_, enum_, "Name", directivesConst {- [lookahead != lcurly_] -}]],

  define "InputObjectTypeDefinition" [
    list[descriptionOpt, input_, "Name", directivesConstOpt, "InputFieldsDefinition"],
    list[descriptionOpt, input_, "Name", directivesConstOpt {- [lookahead != lcurly_] -}]],

  define "InputFieldsDefinition" [
    list[lcurly_, star"InputValueDefinition", rcurly_]],

  define "InputObjectTypeExtension" [
    list[extend_, input_, "Name", directivesConstOpt, "InputFieldsDefinition"],
    list[extend_, input_, "Name", directivesConst {- [lookahead != lcurly_] -}]],

  define "DirectiveDefinition" [
    list[descriptionOpt, directive_, at_, "Name", opt"ArgumentsDefinition", opt(repeatable_), on_, "DirectiveLocations"]],

  define "DirectiveLocations" [
    list["DirectiveLocations", or_, "DirectiveLocation"],
    list[opt(or_), "DirectiveLocation"]],

  define "DirectiveLocation" [
    "executable">: "ExecutableDirectiveLocation",
    "typeSystem">: "TypeSystemDirectiveLocation"],

  define "ExecutableDirectiveLocation" $ terminal <$> [
    "QUERY",
    "MUTATION",
    "SUBSCRIPTION",
    "FIELD",
    "FRAGMENT_DEFINITION",
    "FRAGMENT_SPREAD",
    "INLINE_FRAGMENT",
    "VARIABLE_DEFINITION"],

  define "TypeSystemDirectiveLocation" $ terminal <$> [
    "SCHEMA",
    "SCALAR",
    "OBJECT",
    "FIELD_DEFINITION",
    "ARGUMENT_DEFINITION",
    "INTERFACE",
    "UNION",
    "ENUM",
    "ENUM_VALUE",
    "INPUT_OBJECT",
    "INPUT_FIELD_DEFINITION"]]
