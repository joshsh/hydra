module Hydra.Sources.Tier4.Ext.Csharp.Syntax where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Types as Types
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap


csharpSyntaxModule :: Module
csharpSyntaxModule = Module ns elements [hydraCoreModule] tier0Modules $
    Just ("A C# syntax module based on the ANTLR grammar dated 02/07/2024 and available at:\n"
      ++ "  https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/language-specification/grammar")
  where
    ns = Namespace "hydra/ext/csharp/syntax"
    def = datatype ns
    csharp = typeref ns

    elements = lexicalElements ++ syntacticElements ++ unsafeElements

    lexicalElements = [
-- // Source: §6.3.1 General
-- DEFAULT  : 'default' ;
-- NULL     : 'null' ;
-- TRUE     : 'true' ;
-- FALSE    : 'false' ;
-- ASTERISK : '*' ;
-- SLASH    : '/' ;
--
-- // Source: §6.3.1 General
-- input
--     : input_section?
--     ;
--
-- input_section
--     : input_section_part+
--     ;
--
-- input_section_part
--     : input_element* New_Line
--     | PP_Directive
--     ;
--
-- input_element
--     : Whitespace
--     | Comment
--     | token
--     ;
--
-- // Source: §6.3.2 Line terminators
-- New_Line
--     : New_Line_Character
--     | '\u000D\u000A'    // carriage return, line feed
--     ;
--
-- // Source: §6.3.3 Comments
-- Comment
--     : Single_Line_Comment
--     | Delimited_Comment
--     ;
--
-- fragment Single_Line_Comment
--     : '//' Input_Character*
--     ;
--
-- fragment Input_Character
--     // anything but New_Line_Character
--     : ~('\u000D' | '\u000A'   | '\u0085' | '\u2028' | '\u2029')
--     ;
--
-- fragment New_Line_Character
--     : '\u000D'  // carriage return
--     | '\u000A'  // line feed
--     | '\u0085'  // next line
--     | '\u2028'  // line separator
--     | '\u2029'  // paragraph separator
--     ;
--
-- fragment Delimited_Comment
--     : '/*' Delimited_Comment_Section* ASTERISK+ '/'
--     ;
--
-- fragment Delimited_Comment_Section
--     : SLASH
--     | ASTERISK* Not_Slash_Or_Asterisk
--     ;
--
-- fragment Not_Slash_Or_Asterisk
--     : ~('/' | '*')    // Any except SLASH or ASTERISK
--     ;
--
-- // Source: §6.3.4 White space
-- Whitespace
--     : [\p{Zs}]  // any character with Unicode class Zs
--     | '\u0009'  // horizontal tab
--     | '\u000B'  // vertical tab
--     | '\u000C'  // form feed
--     ;
--
-- // Source: §6.4.1 General
-- token
--     : identifier
--     | keyword
--     | Integer_Literal
--     | Real_Literal
--     | Character_Literal
--     | String_Literal
--     | operator_or_punctuator
--     ;
--
-- // Source: §6.4.2 Unicode character escape sequences
-- fragment Unicode_Escape_Sequence
--     : '\\u' Hex_Digit Hex_Digit Hex_Digit Hex_Digit
--     | '\\U' Hex_Digit Hex_Digit Hex_Digit Hex_Digit
--             Hex_Digit Hex_Digit Hex_Digit Hex_Digit
--     ;
--
-- // Source: §6.4.3 Identifiers
-- identifier
--     : Simple_Identifier
--     | contextual_keyword
--     ;

      def "Identifier" $ wrap
        string,

-- Simple_Identifier
--     : Available_Identifier
--     | Escaped_Identifier
--     ;
--
-- fragment Available_Identifier
--     // excluding keywords or contextual keywords, see note below
--     : Basic_Identifier
--     ;
--
-- fragment Escaped_Identifier
--     // Includes keywords and contextual keywords prefixed by '@'.
--     // See note below.
--     : '@' Basic_Identifier
--     ;
--
-- fragment Basic_Identifier
--     : Identifier_Start_Character Identifier_Part_Character*
--     ;
--
-- fragment Identifier_Start_Character
--     : Letter_Character
--     | Underscore_Character
--     ;
--
-- fragment Underscore_Character
--     : '_'               // underscore
--     | '\\u005' [fF]     // Unicode_Escape_Sequence for underscore
--     | '\\U0000005' [fF] // Unicode_Escape_Sequence for underscore
--     ;
--
-- fragment Identifier_Part_Character
--     : Letter_Character
--     | Decimal_Digit_Character
--     | Connecting_Character
--     | Combining_Character
--     | Formatting_Character
--     ;
--
-- fragment Letter_Character
--     // Category Letter, all subcategories; category Number, subcategory letter.
--     : [\p{L}\p{Nl}]
--     // Only escapes for categories L & Nl allowed. See note below.
--     | Unicode_Escape_Sequence
--     ;
--
-- fragment Combining_Character
--     // Category Mark, subcategories non-spacing and spacing combining.
--     : [\p{Mn}\p{Mc}]
--     // Only escapes for categories Mn & Mc allowed. See note below.
--     | Unicode_Escape_Sequence
--     ;
--
-- fragment Decimal_Digit_Character
--     // Category Number, subcategory decimal digit.
--     : [\p{Nd}]
--     // Only escapes for category Nd allowed. See note below.
--     | Unicode_Escape_Sequence
--     ;
--
-- fragment Connecting_Character
--     // Category Punctuation, subcategory connector.
--     : [\p{Pc}]
--     // Only escapes for category Pc allowed. See note below.
--     | Unicode_Escape_Sequence
--     ;
--
-- fragment Formatting_Character
--     // Category Other, subcategory format.
--     : [\p{Cf}]
--     // Only escapes for category Cf allowed, see note below.
--     | Unicode_Escape_Sequence
--     ;
--
-- // Source: §6.4.4 Keywords
-- keyword
--     : 'abstract' | 'as'       | 'base'       | 'bool'      | 'break'
--     | 'byte'     | 'case'     | 'catch'      | 'char'      | 'checked'
--     | 'class'    | 'const'    | 'continue'   | 'decimal'   | DEFAULT
--     | 'delegate' | 'do'       | 'double'     | 'else'      | 'enum'
--     | 'event'    | 'explicit' | 'extern'     | FALSE       | 'finally'
--     | 'fixed'    | 'float'    | 'for'        | 'foreach'   | 'goto'
--     | 'if'       | 'implicit' | 'in'         | 'int'       | 'interface'
--     | 'internal' | 'is'       | 'lock'       | 'long'      | 'namespace'
--     | 'new'      | NULL       | 'object'     | 'operator'  | 'out'
--     | 'override' | 'params'   | 'private'    | 'protected' | 'public'
--     | 'readonly' | 'ref'      | 'return'     | 'sbyte'     | 'sealed'
--     | 'short'    | 'sizeof'   | 'stackalloc' | 'static'    | 'string'
--     | 'struct'   | 'switch'   | 'this'       | 'throw'     | TRUE
--     | 'try'      | 'typeof'   | 'uint'       | 'ulong'     | 'unchecked'
--     | 'unsafe'   | 'ushort'   | 'using'      | 'virtual'   | 'void'
--     | 'volatile' | 'while'
--     ;

      def "Keyword" $ wrap
        string,

-- // Source: §6.4.4 Keywords
-- contextual_keyword
--     : 'add'    | 'alias'      | 'ascending' | 'async'     | 'await'
--     | 'by'     | 'descending' | 'dynamic'   | 'equals'    | 'from'
--     | 'get'    | 'global'     | 'group'     | 'into'      | 'join'
--     | 'let'    | 'nameof'     | 'on'        | 'orderby'   | 'partial'
--     | 'remove' | 'select'     | 'set'       | 'unmanaged' | 'value'
--     | 'var'    | 'when'       | 'where'     | 'yield'
--     ;
--
-- // Source: §6.4.5.1 General
-- literal
--     : boolean_literal
--     | Integer_Literal
--     | Real_Literal
--     | Character_Literal
--     | String_Literal
--     | null_literal
--     ;

      def "Literal" $ union [
        "boolean">: boolean,
        "integer">: csharp "IntegerLiteral",
        "real">: bigfloat,
        "character">: string,
        "string">: string,
        "null">: unit],

-- // Source: §6.4.5.2 Boolean literals
-- boolean_literal
--     : TRUE
--     | FALSE
--     ;
--
-- // Source: §6.4.5.3 Integer literals
-- Integer_Literal
--     : Decimal_Integer_Literal
--     | Hexadecimal_Integer_Literal
--     | Binary_Integer_Literal
--     ;

      def "IntegerLiteral" $ union [
        "decimal">: string,
        "hexadecimal">: string,
        "binary">: bigint]

-- fragment Decimal_Integer_Literal
--     : Decimal_Digit Decorated_Decimal_Digit* Integer_Type_Suffix?
--     ;
--
-- fragment Decorated_Decimal_Digit
--     : '_'* Decimal_Digit
--     ;
--
-- fragment Decimal_Digit
--     : '0'..'9'
--     ;
--
-- fragment Integer_Type_Suffix
--     : 'U' | 'u' | 'L' | 'l' |
--       'UL' | 'Ul' | 'uL' | 'ul' | 'LU' | 'Lu' | 'lU' | 'lu'
--     ;
--
-- fragment Hexadecimal_Integer_Literal
--     : ('0x' | '0X') Decorated_Hex_Digit+ Integer_Type_Suffix?
--     ;
--
-- fragment Decorated_Hex_Digit
--     : '_'* Hex_Digit
--     ;
--
-- fragment Hex_Digit
--     : '0'..'9' | 'A'..'F' | 'a'..'f'
--     ;
--
-- fragment Binary_Integer_Literal
--     : ('0b' | '0B') Decorated_Binary_Digit+ Integer_Type_Suffix?
--     ;
--
-- fragment Decorated_Binary_Digit
--     : '_'* Binary_Digit
--     ;
--
-- fragment Binary_Digit
--     : '0' | '1'
--     ;
--
-- // Source: §6.4.5.4 Real literals
-- Real_Literal
--     : Decimal_Digit Decorated_Decimal_Digit* '.'
--       Decimal_Digit Decorated_Decimal_Digit* Exponent_Part? Real_Type_Suffix?
--     | '.' Decimal_Digit Decorated_Decimal_Digit* Exponent_Part? Real_Type_Suffix?
--     | Decimal_Digit Decorated_Decimal_Digit* Exponent_Part Real_Type_Suffix?
--     | Decimal_Digit Decorated_Decimal_Digit* Real_Type_Suffix
--     ;
--
-- fragment Exponent_Part
--     : ('e' | 'E') Sign? Decimal_Digit Decorated_Decimal_Digit*
--     ;
--
-- fragment Sign
--     : '+' | '-'
--     ;
--
-- fragment Real_Type_Suffix
--     : 'F' | 'f' | 'D' | 'd' | 'M' | 'm'
--     ;
--
-- // Source: §6.4.5.5 Character literals
-- Character_Literal
--     : '\'' Character '\''
--     ;
--
-- fragment Character
--     : Single_Character
--     | Simple_Escape_Sequence
--     | Hexadecimal_Escape_Sequence
--     | Unicode_Escape_Sequence
--     ;
--
-- fragment Single_Character
--     // anything but ', \, and New_Line_Character
--     : ~['\\\u000D\u000A\u0085\u2028\u2029]
--     ;
--
-- fragment Simple_Escape_Sequence
--     : '\\\'' | '\\"' | '\\\\' | '\\0' | '\\a' | '\\b' |
--       '\\f' | '\\n' | '\\r' | '\\t' | '\\v'
--     ;
--
-- fragment Hexadecimal_Escape_Sequence
--     : '\\x' Hex_Digit Hex_Digit? Hex_Digit? Hex_Digit?
--     ;
--
-- // Source: §6.4.5.6 String literals
-- String_Literal
--     : Regular_String_Literal
--     | Verbatim_String_Literal
--     ;
--
-- fragment Regular_String_Literal
--     : '"' Regular_String_Literal_Character* '"'
--     ;
--
-- fragment Regular_String_Literal_Character
--     : Single_Regular_String_Literal_Character
--     | Simple_Escape_Sequence
--     | Hexadecimal_Escape_Sequence
--     | Unicode_Escape_Sequence
--     ;
--
-- fragment Single_Regular_String_Literal_Character
--     // anything but ", \, and New_Line_Character
--     : ~["\\\u000D\u000A\u0085\u2028\u2029]
--     ;
--
-- fragment Verbatim_String_Literal
--     : '@"' Verbatim_String_Literal_Character* '"'
--     ;
--
-- fragment Verbatim_String_Literal_Character
--     : Single_Verbatim_String_Literal_Character
--     | Quote_Escape_Sequence
--     ;
--
-- fragment Single_Verbatim_String_Literal_Character
--     : ~["]     // anything but quotation mark (U+0022)
--     ;
--
-- fragment Quote_Escape_Sequence
--     : '""'
--     ;
--
-- // Source: §6.4.5.7 The null literal
-- null_literal
--     : NULL
--     ;
--
-- // Source: §6.4.6 Operators and punctuators
-- operator_or_punctuator
--     : '{'  | '}'  | '['  | ']'  | '('   | ')'  | '.'  | ','  | ':'  | ';'
--     | '+'  | '-'  | ASTERISK    | SLASH | '%'  | '&'  | '|'  | '^'  | '!' | '~'
--     | '='  | '<'  | '>'  | '?'  | '??'  | '::' | '++' | '--' | '&&' | '||'
--     | '->' | '==' | '!=' | '<=' | '>='  | '+=' | '-=' | '*=' | '/=' | '%='
--     | '&=' | '|=' | '^=' | '<<' | '<<=' | '=>'
--     ;
--
-- right_shift
--     : '>'  '>'
--     ;
--
-- right_shift_assignment
--     : '>' '>='
--     ;
--
-- // Source: §6.5.1 General
-- PP_Directive
--     : PP_Start PP_Kind PP_New_Line
--     ;
--
-- fragment PP_Kind
--     : PP_Declaration
--     | PP_Conditional
--     | PP_Line
--     | PP_Diagnostic
--     | PP_Region
--     | PP_Pragma
--     | PP_Nullable
--     ;
--
-- // Only recognised at the beginning of a line
-- fragment PP_Start
--     // See note below.
--     : { getCharPositionInLine() == 0 }? PP_Whitespace? '#' PP_Whitespace?
--     ;
--
-- fragment PP_Whitespace
--     : ( [\p{Zs}]  // any character with Unicode class Zs
--       | '\u0009'  // horizontal tab
--       | '\u000B'  // vertical tab
--       | '\u000C'  // form feed
--       )+
--     ;
--
-- fragment PP_New_Line
--     : PP_Whitespace? Single_Line_Comment? New_Line
--     ;
--
-- // Source: §6.5.2 Conditional compilation symbols
-- fragment PP_Conditional_Symbol
--     // Must not be equal to tokens TRUE or FALSE. See note below.
--     : Basic_Identifier
--     ;
--
-- // Source: §6.5.3 Pre-processing expressions
-- fragment PP_Expression
--     : PP_Whitespace? PP_Or_Expression PP_Whitespace?
--     ;
--
-- fragment PP_Or_Expression
--     : PP_And_Expression (PP_Whitespace? '||' PP_Whitespace? PP_And_Expression)*
--     ;
--
-- fragment PP_And_Expression
--     : PP_Equality_Expression (PP_Whitespace? '&&' PP_Whitespace?
--       PP_Equality_Expression)*
--     ;
--
-- fragment PP_Equality_Expression
--     : PP_Unary_Expression (PP_Whitespace? ('==' | '!=') PP_Whitespace?
--       PP_Unary_Expression)*
--     ;
--
-- fragment PP_Unary_Expression
--     : PP_Primary_Expression
--     | '!' PP_Whitespace? PP_Unary_Expression
--     ;
--
-- fragment PP_Primary_Expression
--     : TRUE
--     | FALSE
--     | PP_Conditional_Symbol
--     | '(' PP_Whitespace? PP_Expression PP_Whitespace? ')'
--     ;
--
-- // Source: §6.5.4 Definition directives
-- fragment PP_Declaration
--     : 'define' PP_Whitespace PP_Conditional_Symbol
--     | 'undef' PP_Whitespace PP_Conditional_Symbol
--     ;
--
-- // Source: §6.5.5 Conditional compilation directives
-- fragment PP_Conditional
--     : PP_If_Section
--     | PP_Elif_Section
--     | PP_Else_Section
--     | PP_Endif
--     ;
--
-- fragment PP_If_Section
--     : 'if' PP_Whitespace PP_Expression
--     ;
--
-- fragment PP_Elif_Section
--     : 'elif' PP_Whitespace PP_Expression
--     ;
--
-- fragment PP_Else_Section
--     : 'else'
--     ;
--
-- fragment PP_Endif
--     : 'endif'
--     ;
--
-- // Source: §6.5.6 Diagnostic directives
-- fragment PP_Diagnostic
--     : 'error' PP_Message?
--     | 'warning' PP_Message?
--     ;
--
-- fragment PP_Message
--     : PP_Whitespace Input_Character*
--     ;
--
-- // Source: §6.5.7 Region directives
-- fragment PP_Region
--     : PP_Start_Region
--     | PP_End_Region
--     ;
--
-- fragment PP_Start_Region
--     : 'region' PP_Message?
--     ;
--
-- fragment PP_End_Region
--     : 'endregion' PP_Message?
--     ;
--
-- // Source: §6.5.8 Line directives
-- fragment PP_Line
--     : 'line' PP_Whitespace PP_Line_Indicator
--     ;
--
-- fragment PP_Line_Indicator
--     : Decimal_Digit+ PP_Whitespace PP_Compilation_Unit_Name
--     | Decimal_Digit+
--     | DEFAULT
--     | 'hidden'
--     ;
--
-- fragment PP_Compilation_Unit_Name
--     : '"' PP_Compilation_Unit_Name_Character+ '"'
--     ;
--
-- fragment PP_Compilation_Unit_Name_Character
--     // Any Input_Character except "
--     : ~('\u000D' | '\u000A'   | '\u0085' | '\u2028' | '\u2029' | '#')
--     ;
--
-- // Source: §6.5.9 Nullable directive
-- fragment PP_Nullable
--     : 'nullable' PP_Whitespace PP_Nullable_Action (PP_Whitespace PP_Nullable_Target)?
--     ;
-- fragment PP_Nullable_Action
--     : 'disable'
--     | 'enable'
--     | 'restore'
--     ;
-- fragment PP_Nullable_Target
--     : 'warnings'
--     | 'annotations'
--     ;
--
-- // Source: §6.5.10 Pragma directives
-- fragment PP_Pragma
--     : 'pragma' PP_Pragma_Text?
--     ;
--
-- fragment PP_Pragma_Text
--     : PP_Whitespace Input_Character*
--     ;
      ]

    syntacticElements = [
-- // Source: §7.8.1 General
-- namespace_name
--     : namespace_or_type_name
--     ;

      def "NamespaceName" $ wrap $
        csharp "NamespaceOrTypeName",

-- type_name
--     : namespace_or_type_name
--     ;

      def "TypeName" $ wrap $
        csharp "NamespaceOrTypeName",

-- namespace_or_type_name
--     : identifier type_argument_list?
--     | namespace_or_type_name '.' identifier type_argument_list?
--     | qualified_alias_member
--     ;

        def "NamespaceOrTypeName" $ union [
          "identifier">: csharp "IdentifierNamespaceOrTypeName",
          "qualified">: csharp "QualifiedNamespaceOrTypeName",
          "alias">: csharp "QualifiedAliasMember"],

        def "IdentifierNamespaceOrTypeName" $ record [
          "identifier">: csharp "Identifier",
          "arguments">: optional $ csharp "TypeArgumentList"],

       def "QualifiedNamespaceOrTypeName" $ record [
          "namespaceOrType">: csharp "NamespaceOrTypeName",
          "identifier">: csharp "Identifier",
          "arguments">: optional $ csharp "TypeArgumentList"],

-- // Source: §8.1 General
-- type
--     : reference_type
--     | value_type
--     | type_parameter
--     | pointer_type     // unsafe code support
--     ;

      def "Type" $ union [
        "reference">: csharp "ReferenceType",
        "value">: csharp "ValueType",
        "param">: csharp "TypeParameter",
        "pointer">: csharp "PointerType"],

-- // Source: §8.2.1 General
-- reference_type
--     : class_type
--     | interface_type
--     | array_type
--     | delegate_type
--     | 'dynamic'
--     ;

      def "ReferenceType" $ union [
        "class">: csharp "ClassType",
        "interface">: csharp "InterfaceType",
        "array">: csharp "ArrayType",
        "delegate">: csharp "DelegateType",
        "dynamic">: unit],

-- class_type
--     : type_name
--     | 'object'
--     | 'string'
--     ;

      def "ClassType" $ union [
        "typeName">: csharp "TypeName",
        "object">: unit,
        "string">: unit],

-- interface_type
--     : type_name
--     ;

      def "InterfaceType" $ wrap $
        csharp "TypeName",

-- array_type
--     : non_array_type rank_specifier+
--     ;

      def "ArrayType" $ record [
        "type">: csharp "NonArrayType",
        "rank">: list $ csharp "RankSpecifier"],

-- non_array_type
--     : value_type
--     | class_type
--     | interface_type
--     | delegate_type
--     | 'dynamic'
--     | type_parameter
--     | pointer_type      // unsafe code support
--     ;

      def "NonArrayType" $ union [
        "value">: csharp "ValueType",
        "class">: csharp "ClassType",
        "interface">: csharp "InterfaceType",
        "delegate">: csharp "DelegateType",
        "dynamic">: unit,
        "parameter">: csharp "TypeParameter",
        "pointer">: csharp "PointerType"],

-- rank_specifier
--     : '[' ','* ']'
--     ;

      def "RankSpecifier" $ wrap
        int32, -- Note: non-negative

-- delegate_type
--     : type_name
--     ;

      def "DelegateType" $ wrap $
        csharp "TypeName",

-- // Source: §8.3.1 General
-- value_type
--     : non_nullable_value_type
--     | nullable_value_type
--     ;

      def "ValueType" $ union [
        "nonNullable">: csharp "StructOrEnumType",
        "nullable">: csharp "StructOrEnumType"],

-- non_nullable_value_type
--     : struct_type
--     | enum_type
--     ;

      def "StructOrEnumType" $ union [
        "struct">: csharp "StructType",
        "enum">: csharp "EnumType"],

-- struct_type
--     : type_name
--     | simple_type
--     | tuple_type
--     ;

      def "StructType" $ union [
        "typeName">: csharp "TypeName",
        "simple">: csharp "SimpleType",
        "tuple">: csharp "TupleType"],

-- simple_type
--     : numeric_type
--     | 'bool'
--     ;

      def "SimpleType" $ union [
        "numeric">: csharp "NumericType",
        "bool">: unit],

-- numeric_type
--     : integral_type
--     | floating_point_type
--     | 'decimal'
--     ;

      def "NumericType" $ union [
        "integral">: csharp "IntegralType",
        "floatingPoint">: csharp "FloatingPointType",
        "decimal">: unit],

-- integral_type
--     : 'sbyte'
--     | 'byte'
--     | 'short'
--     | 'ushort'
--     | 'int'
--     | 'uint'
--     | 'long'
--     | 'ulong'
--     | 'char'
--     ;

      def "IntegralType" $ union [
        "sbyte">: unit,
        "byte">: unit,
        "short">: unit,
        "ushort">: unit,
        "int">: unit,
        "uint">: unit,
        "long">: unit,
        "ulong">: unit,
        "char">: unit],

-- floating_point_type
--     : 'float'
--     | 'double'
--     ;

      def "FloatingPointType" $ union [
        "float">: unit,
        "double">: unit],

-- tuple_type
--     : '(' tuple_type_element (',' tuple_type_element)+ ')'
--     ;

      def "TupleType" $ wrap $
        nonemptyList $ csharp "TupleTypeElement",

-- tuple_type_element
--     : type identifier?
--     ;

      def "TupleTypeElement" $ record [
        "type">: csharp "Type",
        "identifier">: optional $ csharp "Identifier"],

-- enum_type
--     : type_name
--     ;

      def "EnumType" $ wrap $
        csharp "TypeName",

-- nullable_value_type
--     : non_nullable_value_type '?'
--     ;
--
-- // Source: §8.4.2 Type arguments
-- type_argument_list
--     : '<' type_arguments '>'
--     ;

      def "TypeArgumentList" $ list $ csharp "Type",

-- type_arguments
--     : type_argument (',' type_argument)*
--     ;
--
-- type_argument
--     : type
--     ;
--
-- // Source: §8.5 Type parameters
-- type_parameter
--     : identifier
--     ;

      def "TypeParameter" $ wrap $
        csharp "Identifier",

-- // Source: §8.8 Unmanaged types
-- unmanaged_type
--     : value_type
--     | pointer_type     // unsafe code support
--     ;

      def "UnmanagedType" $ union [
        "value">: csharp "ValueType",
        "pointer">: csharp "PointerType"],

-- // Source: §9.5 Variable references
-- variable_reference
--     : expression
--     ;

      def "VariableReference" $ wrap $
        csharp "Expression",

-- // Source: §11.2.1 General
-- pattern
--     : declaration_pattern
--     | constant_pattern
--     | var_pattern
--     ;

      def "Pattern" $ union [
        "declaration">: csharp "DeclarationPattern",
        "constant">: csharp "Expression",
        "var">: csharp "Designation"],

-- // Source: §11.2.2 Declaration pattern
-- declaration_pattern
--     : type simple_designation
--     ;

      def "DeclarationPattern" $ record [
        "type">: csharp "Type",
        "designation">: csharp "Designation"],

-- simple_designation
--     : single_variable_designation
--     ;

      def "Designation" $ wrap $
        csharp "Identifier",

-- single_variable_designation
--     : identifier
--     ;
--
-- // Source: §11.2.3 Constant pattern
-- constant_pattern
--     : constant_expression
--     ;
--
-- // Source: §11.2.4 Var pattern
-- var_pattern
--     : 'var' designation
--     ;
-- designation
--     : simple_designation
--     ;
--
-- // Source: §12.6.2.1 General
-- argument_list
--     : argument (',' argument)*
--     ;

      def "ArgumentList" $ nonemptyList $ csharp "Argument",

-- argument
--     : argument_name? argument_value
--     ;

      def "Argument" $ record [
        "name">: optional $ csharp "Identifier",
        "value">: csharp "ArgumentValue"],

-- argument_name
--     : identifier ':'
--     ;
--
-- argument_value
--     : expression
--     | 'in' variable_reference
--     | 'ref' variable_reference
--     | 'out' variable_reference
--     ;

      def "ArgumentValue" $ union [
        "expression">: csharp "Expression",
        "in">: csharp "VariableReference",
        "ref">: csharp "VariableReference",
        "out">: csharp "VariableReference"],

-- // Source: §12.8.1 General
-- primary_expression
--     : primary_no_array_creation_expression
--     | array_creation_expression
--     ;

      def "PrimaryExpression" $ union [
        "noArray">: csharp "PrimaryNoArrayCreationExpression",
        "array">: csharp "ArrayCreationExpression"],

-- primary_no_array_creation_expression
--     : literal
--     | interpolated_string_expression
--     | simple_name
--     | parenthesized_expression
--     | tuple_expression
--     | member_access
--     | null_conditional_member_access
--     | invocation_expression
--     | element_access
--     | null_conditional_element_access
--     | this_access
--     | base_access
--     | post_increment_expression
--     | post_decrement_expression
--     | object_creation_expression
--     | delegate_creation_expression
--     | anonymous_object_creation_expression
--     | typeof_expression
--     | sizeof_expression
--     | checked_expression
--     | unchecked_expression
--     | default_value_expression
--     | nameof_expression
--     | anonymous_method_expression
--     | pointer_member_access     // unsafe code support
--     | pointer_element_access    // unsafe code support
--     | stackalloc_expression
--     ;

      def "PrimaryNoArrayCreationExpression" $ union [
        "literal">: csharp "Literal",
        "interpolatedString">: csharp "InterpolatedStringExpression",
        "simpleName">: csharp "SimpleName",
        "parenthesized">: csharp "Expression",
        "tuple">: csharp "TupleExpression",
        "memberAccess">: csharp "MemberAccess",
        "nullConditionalMemberAccess">: csharp "NullConditionalMemberAccess",
        "invocation">: csharp "InvocationExpression",
        "elementAccess">: csharp "ElementAccess",
        "nullConditionalElementAccess">: csharp "NullConditionalElementAccess",
        "thisAccess">: unit,
        "baseAccess">: csharp "BaseAccess",
        "postIncrement">: csharp "PrimaryExpression",
        "postDecrement">: csharp "PrimaryExpression",
        "objectCreation">: csharp "ObjectCreationExpression",
        "delegateCreation">: csharp "DelegateCreationExpression",
        "anonymousObjectCreation">: optional $ csharp "MemberDeclaratorList",
        "typeof">: csharp "TypeofExpression",
        "sizeof">: csharp "UnmanagedType",
        "checked">: csharp "Expression",
        "unchecked">: csharp "Expression",
        "defaultValue">: csharp "DefaultValueExpression",
        "nameof">: csharp "NamedEntity",
        "anonymousMethod">: csharp "AnonymousMethodExpression",
        "pointerMemberAccess">: csharp "PointerMemberAccess",
        "pointerElementAccess">: csharp "PointerElementAccess",
        "stackalloc">: csharp "StackallocExpression"],

-- // Source: §12.8.3 Interpolated string expressions
-- interpolated_string_expression
--     : interpolated_regular_string_expression
--     | interpolated_verbatim_string_expression
--     ;

      def "InterpolatedStringExpression" $ union [
        "regular">: csharp "InterpolatedRegularStringExpression",
        "verbatim">: csharp "InterpolatedVerbatimStringExpression"],

-- // interpolated regular string expressions
--
-- interpolated_regular_string_expression
--     : Interpolated_Regular_String_Start Interpolated_Regular_String_Mid?
--       ('{' regular_interpolation '}' Interpolated_Regular_String_Mid?)*
--       Interpolated_Regular_String_End
--     ;

      def "InterpolatedRegularStringExpression" $ wrap
        string,

-- regular_interpolation
--     : expression (',' interpolation_minimum_width)?
--       Regular_Interpolation_Format?
--     ;

      def "RegularInterpolation" $ record [
        "expression">: csharp "Expression",
        "width">: optional $ csharp "Expression",
        "format">: optional string],

-- interpolation_minimum_width
--     : constant_expression
--     ;
--
-- Interpolated_Regular_String_Start
--     : '$"'
--     ;
--
-- // the following three lexical rules are context sensitive, see details below
--
-- Interpolated_Regular_String_Mid
--     : Interpolated_Regular_String_Element+
--     ;
--
-- Regular_Interpolation_Format
--     : ':' Interpolated_Regular_String_Element+
--     ;
--
-- Interpolated_Regular_String_End
--     : '"'
--     ;
--
-- fragment Interpolated_Regular_String_Element
--     : Interpolated_Regular_String_Character
--     | Simple_Escape_Sequence
--     | Hexadecimal_Escape_Sequence
--     | Unicode_Escape_Sequence
--     | Open_Brace_Escape_Sequence
--     | Close_Brace_Escape_Sequence
--     ;
--
-- fragment Interpolated_Regular_String_Character
--     // Any character except " (U+0022), \\ (U+005C),
--     // { (U+007B), } (U+007D), and New_Line_Character.
--     : ~["\\{}\u000D\u000A\u0085\u2028\u2029]
--     ;
--
-- // interpolated verbatim string expressions
--
-- interpolated_verbatim_string_expression
--     : Interpolated_Verbatim_String_Start Interpolated_Verbatim_String_Mid?
--       ('{' verbatim_interpolation '}' Interpolated_Verbatim_String_Mid?)*
--       Interpolated_Verbatim_String_End
--     ;

      def "InterpolatedVerbatimStringExpression" $ wrap
        string,

-- verbatim_interpolation
--     : expression (',' interpolation_minimum_width)?
--       Verbatim_Interpolation_Format?
--     ;

      def "VerbatimInterpolation" $ record [
        "expression">: csharp "Expression",
        "width">: optional $ csharp "ConstantExpression",
        "format">: optional string],

-- Interpolated_Verbatim_String_Start
--     : '$@"'
--     | '@$"'
--     ;
--
-- // the following three lexical rules are context sensitive, see details below
--
-- Interpolated_Verbatim_String_Mid
--     : Interpolated_Verbatim_String_Element+
--     ;
--
-- Verbatim_Interpolation_Format
--     : ':' Interpolated_Verbatim_String_Element+
--     ;
--
-- Interpolated_Verbatim_String_End
--     : '"'
--     ;
--
-- fragment Interpolated_Verbatim_String_Element
--     : Interpolated_Verbatim_String_Character
--     | Quote_Escape_Sequence
--     | Open_Brace_Escape_Sequence
--     | Close_Brace_Escape_Sequence
--     ;
--
-- fragment Interpolated_Verbatim_String_Character
--     : ~["{}]    // Any character except " (U+0022), { (U+007B) and } (U+007D)
--     ;
--
-- // lexical fragments used by both regular and verbatim interpolated strings
--
-- fragment Open_Brace_Escape_Sequence
--     : '{{'
--     ;
--
-- fragment Close_Brace_Escape_Sequence
--     : '}}'
--     ;
--
-- // Source: §12.8.4 Simple names
-- simple_name
--     : identifier type_argument_list?
--     ;

      def "SimpleName" $ record [
        "identifier">: csharp "Identifier",
        "typeArguments">: optional $ csharp "TypeArgumentList"],

-- // Source: §12.8.5 Parenthesized expressions
-- parenthesized_expression
--     : '(' expression ')'
--     ;
--
-- // Source: §12.8.6 Tuple expressions
-- tuple_expression
--     : '(' tuple_element (',' tuple_element)+ ')'
--     | deconstruction_expression
--     ;

      def "TupleExpression" $ union [
        "elements">: nonemptyList $ csharp "TupleElement",
        "deconstruction">: csharp "DeconstructionTuple"],

-- tuple_element
--     : (identifier ':')? expression
--     ;

      def "TupleElement" $ record [
        "name">: optional $ csharp "Identifier",
        "expression">: csharp "Expression"],

-- deconstruction_expression
--     : 'var' deconstruction_tuple
--     ;
--
-- deconstruction_tuple
--     : '(' deconstruction_element (',' deconstruction_element)+ ')'
--     ;

      def "DeconstructionTuple" $ wrap $
        nonemptyList $ csharp "DeconstructionElement",

-- deconstruction_element
--     : deconstruction_tuple
--     | identifier
--     ;

      def "DeconstructionElement" $ union [
        "tuple">: csharp "DeconstructionTuple",
        "identifier">: csharp "Identifier"],

-- // Source: §12.8.7.1 General
-- member_access
--     : primary_expression '.' identifier type_argument_list?
--     | predefined_type '.' identifier type_argument_list?
--     | qualified_alias_member '.' identifier type_argument_list?
--     ;

      def "MemberAccess" $ record [
        "head">: csharp "MemberAccessHead",
        "identifier">: csharp "Identifier",
        "typeArguments">: optional $ csharp "TypeArgumentList"],

      def "MemberAccessHead" $ union [
        "primary">: csharp "PrimaryExpression",
        "predefined">: csharp "PredefinedType",
        "qualifiedAlias">: csharp "QualifiedAliasMember"],

-- predefined_type
--     : 'bool' | 'byte' | 'char' | 'decimal' | 'double' | 'float' | 'int'
--     | 'long' | 'object' | 'sbyte' | 'short' | 'string' | 'uint' | 'ulong'
--     | 'ushort'
--     ;

      def "PredefinedType" $ enum [
        "bool", "byte", "char", "decimal", "double", "float", "int", "long", "object", "sbyte", "short", "string",
        "uint", "ulong", "ushort"],

-- // Source: §12.8.8 Null Conditional Member Access
-- null_conditional_member_access
--     : primary_expression '?' '.' identifier type_argument_list?
--       dependent_access*
--     ;

      def "NullConditionalMemberAccess" $ record [
        "expression">: csharp "PrimaryExpression",
        "identifier">: csharp "Identifier",
        "typeArguments">: optional $ csharp "TypeArgumentList",
        "dependentAccess">: list $ csharp "DependentAccess"],

-- dependent_access
--     : '.' identifier type_argument_list?    // member access
--     | '[' argument_list ']'                 // element access
--     | '(' argument_list? ')'                // invocation
--     ;

      def "DependentAccess" $ union [
        "memberAccess">: csharp "DependentAccessForMember",
        "elementAccess">: csharp "ArgumentList",
        "invocation">: optional $ csharp "ArgumentList"],

      def "DependentAccessForMember" $ record [
        "identifier">: csharp "Identifier",
        "typeArguments">: optional $ csharp "TypeArgumentList"],

-- null_conditional_projection_initializer
--     : primary_expression '?' '.' identifier type_argument_list?
--     ;

      def "NullConditionalProjectionInitializer" $ record [
        "expression">: csharp "PrimaryExpression",
        "identifier">: csharp "Identifier",
        "typeArguments">: optional $ csharp "TypeArgumentList"],

-- // Source: §12.8.9.1 General
-- invocation_expression
--     : primary_expression '(' argument_list? ')'
--     ;

      def "InvocationExpression" $ record [
        "expression">: csharp "PrimaryExpression",
        "arguments">: optional $ csharp "ArgumentList"],

-- // Source: §12.8.10 Null Conditional Invocation Expression
-- null_conditional_invocation_expression
--     : null_conditional_member_access '(' argument_list? ')'
--     | null_conditional_element_access '(' argument_list? ')'
--     ;

      def "NullConditionalInvocationExpression" $ record [
        "head">: csharp "NullConditionalInvocationExpressionHead",
        "arguments">: optional $ csharp "ArgumentList"],

      def "NullConditionalInvocationExpressionHead" $ union [
        "member">: csharp "NullConditionalMemberAccess",
        "element">: csharp "NullConditionalElementAccess"],

-- // Source: §12.8.11.1 General
-- element_access
--     : primary_no_array_creation_expression '[' argument_list ']'
--     ;

      def "ElementAccess" $ record [
        "expression">: csharp "PrimaryNoArrayCreationExpression",
        "arguments">: csharp "ArgumentList"],

-- // Source: §12.8.12 Null Conditional Element Access
-- null_conditional_element_access
--     : primary_no_array_creation_expression '?' '[' argument_list ']'
--       dependent_access*
--     ;

      def "NullConditionalElementAccess" $ record [
        "expression">: csharp "PrimaryNoArrayCreationExpression",
        "arguments">: csharp "ArgumentList",
        "dependentAccess">: list $ csharp "DependentAccess"],

-- // Source: §12.8.13 This access
-- this_access
--     : 'this'
--     ;
--
-- // Source: §12.8.14 Base access
-- base_access
--     : 'base' '.' identifier type_argument_list?
--     | 'base' '[' argument_list ']'
--     ;

      def "BaseAccess" $ union [
        "identifier">: csharp "BaseAccessWithIdentifier",
        "arguments">: csharp "ArgumentList"],

      def "BaseAccessWithIdentifier" $ record [
        "identifier">: csharp "Identifier",
        "typeArguments">: optional $ csharp "TypeArgumentList"],

-- // Source: §12.8.15 Postfix increment and decrement operators
-- post_increment_expression
--     : primary_expression '++'
--     ;
--
-- post_decrement_expression
--     : primary_expression '--'
--     ;
--
-- // Source: §12.8.16.2 Object creation expressions
-- object_creation_expression
--     : 'new' type '(' argument_list? ')' object_or_collection_initializer?
--     | 'new' type object_or_collection_initializer
--     ;

      def "ObjectCreationExpression" $ record [
        "type">: csharp "Type",
        "arguments">: optional $ csharp "ArgumentList",
        "initializer">: optional $ csharp "ObjectOrCollectionInitializer"],

-- object_or_collection_initializer
--     : object_initializer
--     | collection_initializer
--     ;

      def "ObjectOrCollectionInitializer" $ union [
        "object">: list $ csharp "MemberInitializer",
        "collection">: list $ csharp "ElementInitializer"],

-- // Source: §12.8.16.3 Object initializers
-- object_initializer
--     : '{' member_initializer_list? '}'
--     | '{' member_initializer_list ',' '}'
--     ;
--
-- member_initializer_list
--     : member_initializer (',' member_initializer)*
--     ;
--
-- member_initializer
--     : initializer_target '=' initializer_value
--     ;

      def "MemberInitializer" $ record [
        "target">: csharp "InitializerTarget",
        "value">: csharp "InitializerValue"],

-- initializer_target
--     : identifier
--     | '[' argument_list ']'
--     ;

      def "InitializerTarget" $ union [
        "identifier">: csharp "Identifier",
        "arguments">: csharp "ArgumentList"],

-- initializer_value
--     : expression
--     | object_or_collection_initializer
--     ;

      def "InitializerValue" $ union [
        "expression">: csharp "Expression",
        "objectOrCollection">: csharp "ObjectOrCollectionInitializer"],

-- // Source: §12.8.16.4 Collection initializers
-- collection_initializer
--     : '{' element_initializer_list '}'
--     | '{' element_initializer_list ',' '}'
--     ;
--
-- element_initializer_list
--     : element_initializer (',' element_initializer)*
--     ;
--
-- element_initializer
--     : non_assignment_expression
--     | '{' expression_list '}'
--     ;

      def "ElementInitializer" $ union [
        "single">: csharp "NonAssignmentExpression",
        "list">: csharp "ExpressionList"],

-- expression_list
--     : expression
--     | expression_list ',' expression
--     ;

      def "ExpressionList" $ nonemptyList $ csharp "Expression",

-- // Source: §12.8.16.5 Array creation expressions
-- array_creation_expression
--     : 'new' non_array_type '[' expression_list ']' rank_specifier*
--       array_initializer?
--     | 'new' array_type array_initializer
--     | 'new' rank_specifier array_initializer
--     ;

      def "ArrayCreationExpression" $ union [
        "nonArrayType">: csharp "NonArrayTypeArrayCreationExpression",
        "arrayType">: csharp "ArrayTypeArrayCreationExpression",
        "rankSpecifier">: csharp "RankSpecifierArrayCreationExpression"],

      def "NonArrayTypeArrayCreationExpression" $ record [
        "type">: csharp "NonArrayType",
        "expressions">: csharp "ExpressionList",
        "rankSpecifiers">: list $ csharp "RankSpecifier",
        "initializer">: optional $ csharp "ArrayInitializer"],

      def "ArrayTypeArrayCreationExpression" $ record [
        "type">: csharp "ArrayType",
        "initializer">: csharp "ArrayInitializer"],

      def "RankSpecifierArrayCreationExpression" $ record [
        "rankSpecifier">: csharp "RankSpecifier",
        "initializer">: csharp "ArrayInitializer"],

-- // Source: §12.8.16.6 Delegate creation expressions
-- delegate_creation_expression
--     : 'new' delegate_type '(' expression ')'
--     ;

      def "DelegateCreationExpression" $ record [
        "type">: csharp "DelegateType",
        "expression">: csharp "Expression"],

-- // Source: §12.8.16.7 Anonymous object creation expressions
-- anonymous_object_creation_expression
--     : 'new' anonymous_object_initializer
--     ;
--
-- anonymous_object_initializer
--     : '{' member_declarator_list? '}'
--     | '{' member_declarator_list ',' '}'
--     ;
--
-- member_declarator_list
--     : member_declarator (',' member_declarator)*
--     ;

      def "MemberDeclaratorList" $ nonemptyList $ csharp "MemberDeclarator",

-- member_declarator
--     : simple_name
--     | member_access
--     | null_conditional_projection_initializer
--     | base_access
--     | identifier '=' expression
--     ;

      def "MemberDeclarator" $ union [
        "name">: csharp "SimpleName",
        "memberAccess">: csharp "MemberAccess",
        "nullConditionalProjectionInitializer">: csharp "NullConditionalProjectionInitializer",
        "baseAccess">: csharp "BaseAccess",
        "assignment">: csharp "AssignmentMemberDeclarator"],

      def "AssignmentMemberDeclarator" $ record [
        "identifier">: csharp "Identifier",
        "expression">: csharp "Expression"],

-- // Source: §12.8.17 The typeof operator
-- typeof_expression
--     : 'typeof' '(' type ')'
--     | 'typeof' '(' unbound_type_name ')'
--     | 'typeof' '(' 'void' ')'
--     ;

      def "TypeofExpression" $ union [
        "type">: csharp "Type",
        "unboundTypeName">: csharp "UnboundTypeName",
        "void">: unit],

-- unbound_type_name
--     : identifier generic_dimension_specifier?
--     | identifier '::' identifier generic_dimension_specifier?
--     | unbound_type_name '.' identifier generic_dimension_specifier?
--     ;

      def "UnboundTypeName" $ wrap $
        nonemptyList $ csharp "UnboundTypeNamePart",

      def "UnboundTypeNamePart" $ record [
        "identifier">: csharp "Identifier",
        "aliased">: boolean,
        "dimension">: optional int32], -- Note: non-negative

-- generic_dimension_specifier
--     : '<' comma* '>'
--     ;
-- comma
--     : ','
--     ;
--
--
-- // Source: §12.8.18 The sizeof operator
-- sizeof_expression
--     : 'sizeof' '(' unmanaged_type ')'
--     ;
--
-- // Source: §12.8.19 The checked and unchecked operators
-- checked_expression
--     : 'checked' '(' expression ')'
--     ;
--
-- unchecked_expression
--     : 'unchecked' '(' expression ')'
--     ;
--
-- // Source: §12.8.20 Default value expressions
-- default_value_expression
--     : explictly_typed_default
--     | default_literal
--     ;

      def "DefaultValueExpression" $ union [
        "explicitlyTyped">: csharp "Type",
        "defaultLiteral">: unit],

-- explictly_typed_default
--     : 'default' '(' type ')'
--     ;
--
-- default_literal
--     : 'default'
--     ;
--
-- // Source: §12.8.21 Stack allocation
-- stackalloc_expression
--     : 'stackalloc' unmanaged_type '[' expression ']'
--     | 'stackalloc' unmanaged_type? '[' constant_expression? ']'
--       stackalloc_initializer
--     ;

      def "StackallocExpression" $ record [
        "type">: optional $ csharp "UnmanagedType",
        "expression">: optional $ csharp "ConstantExpression",
        "initializer">: list $ csharp "Expression"],

-- stackalloc_initializer
--      : '{' stackalloc_initializer_element_list '}'
--      ;
--
-- stackalloc_initializer_element_list
--      : stackalloc_element_initializer (',' stackalloc_element_initializer)* ','?
--      ;
--
-- stackalloc_element_initializer
--     : expression
--     ;
--
-- // Source: §12.8.22 The nameof operator
-- nameof_expression
--     : 'nameof' '(' named_entity ')'
--     ;
--
-- named_entity
--     : named_entity_target ('.' identifier type_argument_list?)*
--     ;

      def "NamedEntity" $ record [
        "target">: csharp "NamedEntityTarget",
        "parts">: list $ csharp "NamedEntityPart"],

      def "NamedEntityPart" $ record [
        "identifier">: csharp "Identifier",
        "typeArguments">: optional $ csharp "TypeArgumentList"],

-- named_entity_target
--     : simple_name
--     | 'this'
--     | 'base'
--     | predefined_type
--     | qualified_alias_member
--     ;

      def "NamedEntityTarget" $ union [
        "name">: csharp "SimpleName",
        "this">: unit,
        "base">: unit,
        "predefinedType">: csharp "PredefinedType",
        "qualifiedAliasMember">: csharp "QualifiedAliasMember"],

-- // Source: §12.9.1 General
-- unary_expression
--     : primary_expression
--     | '+' unary_expression
--     | '-' unary_expression
--     | '!' unary_expression
--     | '~' unary_expression
--     | pre_increment_expression
--     | pre_decrement_expression
--     | cast_expression
--     | await_expression
--     | pointer_indirection_expression    // unsafe code support
--     | addressof_expression              // unsafe code support
--     ;

      def "UnaryExpression" $ union [
        "primary">: csharp "PrimaryExpression",
        "plus">: csharp "UnaryExpression",
        "minus">: csharp "UnaryExpression",
        "not">: csharp "UnaryExpression",
        "bitwiseComplement">: csharp "UnaryExpression",
        "preIncrement">: csharp "UnaryExpression",
        "preDecrement">: csharp "UnaryExpression",
        "cast">: csharp "CastExpression",
        "await">: csharp "UnaryExpression",
        "pointerIndirection">: csharp "UnaryExpression",
        "addressOf">: csharp "UnaryExpression"],

-- // Source: §12.9.6 Prefix increment and decrement operators
-- pre_increment_expression
--     : '++' unary_expression
--     ;
--
-- pre_decrement_expression
--     : '--' unary_expression
--     ;
--
-- // Source: §12.9.7 Cast expressions
-- cast_expression
--     : '(' type ')' unary_expression
--     ;

      def "CastExpression" $ record [
        "type">: csharp "Type",
        "expression">: csharp "UnaryExpression"],

-- // Source: §12.9.8.1 General
-- await_expression
--     : 'await' unary_expression
--     ;
--
-- // Source: §12.10.1 General
-- multiplicative_expression
--     : unary_expression
--     | multiplicative_expression '*' unary_expression
--     | multiplicative_expression '/' unary_expression
--     | multiplicative_expression '%' unary_expression
--     ;

      def "MultiplicativeExpression" $ union [
        "simple">: csharp "UnaryExpression",
        "binary">: csharp "BinaryMultiplicativeExpression"],

      def "BinaryMultiplicativeExpression" $ record [
        "left">: csharp "MultiplicativeExpression",
        "operator">: csharp "MultiplicativeOperator",
        "right">: csharp "UnaryExpression"],

      def "MultiplicativeOperator" $ enum [
        "times",
        "divide",
        "modulo"],

-- additive_expression
--     : multiplicative_expression
--     | additive_expression '+' multiplicative_expression
--     | additive_expression '-' multiplicative_expression
--     ;

      def "AdditiveExpression" $ union [
        "simple">: csharp "MultiplicativeExpression",
        "binary">: csharp "BinaryAdditiveExpression"],

      def "BinaryAdditiveExpression" $ record [
        "left">: csharp "AdditiveExpression",
        "operator">: csharp "AdditiveOperator",
        "right">: csharp "MultiplicativeExpression"],

      def "AdditiveOperator" $ enum [
        "plus",
        "minus"],

-- // Source: §12.11 Shift operators
-- shift_expression
--     : additive_expression
--     | shift_expression '<<' additive_expression
--     | shift_expression right_shift additive_expression
--     ;

      def "ShiftExpression" $ union [
        "simple">: csharp "AdditiveExpression",
        "binary">: csharp "BinaryShiftExpression"],

      def "BinaryShiftExpression" $ record [
        "left">: csharp "ShiftExpression",
        "operator">: csharp "ShiftOperator",
        "right">: csharp "AdditiveExpression"],

      def "ShiftOperator" $ enum [
        "left",
        "right"],

-- // Source: §12.12.1 General
-- relational_expression
--     : shift_expression
--     | relational_expression '<' shift_expression
--     | relational_expression '>' shift_expression
--     | relational_expression '<=' shift_expression
--     | relational_expression '>=' shift_expression
--     | relational_expression 'is' type
--     | relational_expression 'is' pattern
--     | relational_expression 'as' type
--     ;

      def "RelationalExpression" $ union [
        "simple">: csharp "ShiftExpression",
        "binary">: csharp "BinaryRelationalExpression",
        "isType">: csharp "IsTypeExpression",
        "isPattern">: csharp "IsPatternExpression",
        "asType">: csharp "AsTypeExpression"],

      def "BinaryRelationalExpression" $ record [
       "left">: csharp "RelationalExpression",
        "operator">: csharp "RelationalOperator",
        "right">: csharp "ShiftExpression"],

      def "RelationalOperator" $ enum [
        "lessThan", "greaterThan", "lessThanOrEqual", "greaterThanOrEqual"],

      def "IsTypeExpression" $ record [
       "expression">: csharp "RelationalExpression",
        "type">: csharp "Type"],

      def "IsPatternExpression" $ record [
        "expression">: csharp "RelationalExpression",
        "pattern">: csharp "Pattern"],

      def "AsTypeExpression" $ record [
        "expression">: csharp "RelationalExpression",
        "type">: csharp "Type"],

-- equality_expression
--     : relational_expression
--     | equality_expression '==' relational_expression
--     | equality_expression '!=' relational_expression
--     ;

      def "EqualityExpression" $ union [
        "simple">: csharp "RelationalExpression",
        "binary">: csharp "BinaryEqualityExpression"],

      def "BinaryEqualityExpression" $ record [
        "left">: csharp "EqualityExpression",
        "operator">: csharp "EqualityOperator",
        "right">: csharp "RelationalExpression"],

      def "EqualityOperator" $ enum [
        "equal",
        "notEqual"],

-- // Source: §12.13.1 General
-- and_expression
--     : equality_expression
--     | and_expression '&' equality_expression
--     ;

      def "AndExpression" $ union [
        "simple">: csharp "EqualityExpression",
        "binary">: csharp "BinaryAndExpression"],

      def "BinaryAndExpression" $ record [
        "left">: csharp "AndExpression",
        "right">: csharp "EqualityExpression"],

-- exclusive_or_expression
--     : and_expression
--     | exclusive_or_expression '^' and_expression
--     ;

      def "ExclusiveOrExpression" $ union [
        "simple">: csharp "AndExpression",
        "binary">: csharp "BinaryExclusiveOrExpression"],

      def "BinaryExclusiveOrExpression" $ record [
        "left">: csharp "ExclusiveOrExpression",
        "right">: csharp "AndExpression"],

-- inclusive_or_expression
--     : exclusive_or_expression
--     | inclusive_or_expression '|' exclusive_or_expression
--     ;

      def "InclusiveOrExpression" $ union [
        "simple">: csharp "ExclusiveOrExpression",
        "binary">: csharp "BinaryInclusiveOrExpression"],

      def "BinaryInclusiveOrExpression" $ record [
        "left">: csharp "InclusiveOrExpression",
        "right">: csharp "ExclusiveOrExpression"],

-- // Source: §12.14.1 General
-- conditional_and_expression
--     : inclusive_or_expression
--     | conditional_and_expression '&&' inclusive_or_expression
--     ;

      def "ConditionalAndExpression" $ union [
        "simple">: csharp "InclusiveOrExpression",
        "binary">: csharp "BinaryConditionalAndExpression"],

      def "BinaryConditionalAndExpression" $ record [
        "left">: csharp "ConditionalAndExpression",
        "right">: csharp "InclusiveOrExpression"],

-- conditional_or_expression
--     : conditional_and_expression
--     | conditional_or_expression '||' conditional_and_expression
--     ;

      def "ConditionalOrExpression" $ union [
        "simple">: csharp "ConditionalAndExpression",
        "binary">: csharp "BinaryConditionalOrExpression"],

      def "BinaryConditionalOrExpression" $ record [
        "left">: csharp "ConditionalOrExpression",
        "right">: csharp "ConditionalAndExpression"],

-- // Source: §12.15 The null coalescing operator
-- null_coalescing_expression
--     : conditional_or_expression
--     | conditional_or_expression '??' null_coalescing_expression
--     | throw_expression
--     ;

      def "NullCoalescingExpression" $ union [
        "simple">: csharp "ConditionalOrExpression",
        "binary">: csharp "BinaryNullCoalescingExpression",
        "throw">: csharp "NullCoalescingExpression"],

      def "BinaryNullCoalescingExpression" $ record [
        "left">: csharp "ConditionalOrExpression",
        "right">: csharp "NullCoalescingExpression"],

-- // Source: §12.16 The throw expression operator
-- throw_expression
--     : 'throw' null_coalescing_expression
--     ;
--
-- // Source: §12.17 Declaration expressions
-- declaration_expression
--     : local_variable_type identifier
--     ;

      def "DeclarationExpression" $ record [
        "type">: csharp "LocalVariableType",
        "identifier">: csharp "Identifier"],

-- local_variable_type
--     : type
--     | 'var'
--     ;

      def "LocalVariableType" $ union [
        "type">: csharp "Type",
        "var">: unit],

-- // Source: §12.18 Conditional operator
-- conditional_expression
--     : null_coalescing_expression
--     | null_coalescing_expression '?' expression ':' expression
--     | null_coalescing_expression '?' 'ref' variable_reference ':'
--       'ref' variable_reference
--     ;

      def "ConditionalExpression" $ union [
        "simple">: csharp "NullCoalescingExpression",
        "simpleConditional">: csharp "SimpleConditionalExpression",
        "refConditional">: csharp "RefConditionalExpression"],

      def "SimpleConditionalExpression" $ record [
        "condition">: csharp "NullCoalescingExpression",
        "true">: csharp "Expression",
        "false">: csharp "Expression"],

      def "RefConditionalExpression" $ record [
        "condition">: csharp "NullCoalescingExpression",
        "true">: csharp "VariableReference",
        "false">: csharp "VariableReference"],

-- // Source: §12.19.1 General
-- lambda_expression
--     : 'async'? anonymous_function_signature '=>' anonymous_function_body
--     ;

      def "LambdaExpression" $ record [
        "async">: boolean,
        "signature">: csharp "AnonymousFunctionSignature",
        "body">: csharp "AnonymousFunctionBody"],

-- anonymous_method_expression
--     : 'async'? 'delegate' explicit_anonymous_function_signature? block
--     ;

      def "AnonymousMethodExpression" $ record [
        "async">: boolean,
        "signature">: list $ csharp "ExplicitAnonymousFunctionParameter",
        "body">: csharp "Block"],

-- anonymous_function_signature
--     : explicit_anonymous_function_signature
--     | implicit_anonymous_function_signature
--     ;

      def "AnonymousFunctionSignature" $ union [
        "explicit">: list $ csharp "ExplicitAnonymousFunctionParameter",
        "implicit">: list $ csharp "Identifier"],

-- explicit_anonymous_function_signature
--     : '(' explicit_anonymous_function_parameter_list? ')'
--     ;
--
-- explicit_anonymous_function_parameter_list
--     : explicit_anonymous_function_parameter
--       (',' explicit_anonymous_function_parameter)*
--     ;
--
-- explicit_anonymous_function_parameter
--     : anonymous_function_parameter_modifier? type identifier
--     ;

      def "ExplicitAnonymousFunctionParameter" $ record [
        "modifier">: optional $ csharp "AnonymousFunctionParameterModifier",
        "type">: csharp "Type",
        "identifier">: csharp "Identifier"],

-- anonymous_function_parameter_modifier
--     : 'ref'
--     | 'out'
--     | 'in'
--     ;

      def "AnonymousFunctionParameterModifier" $ enum [
        "ref",
        "out",
        "in"],

-- implicit_anonymous_function_signature
--     : '(' implicit_anonymous_function_parameter_list? ')'
--     | implicit_anonymous_function_parameter
--     ;
--
-- implicit_anonymous_function_parameter_list
--     : implicit_anonymous_function_parameter
--       (',' implicit_anonymous_function_parameter)*
--     ;
--
-- implicit_anonymous_function_parameter
--     : identifier
--     ;
--
-- anonymous_function_body
--     : null_conditional_invocation_expression
--     | expression
--     | 'ref' variable_reference
--     | block
--     ;

      def "AnonymousFunctionBody" $ union [
        "nullConditionalInvocation">: csharp "NullConditionalInvocationExpression",
        "expression">: csharp "Expression",
        "ref">: csharp "VariableReference",
        "block">: csharp "Block"],

-- // Source: §12.20.1 General
-- query_expression
--     : from_clause query_body
--     ;

      def "QueryExpression" $ record [
        "from">: csharp "FromClause",
        "body">: csharp "QueryBody"],

-- from_clause
--     : 'from' type? identifier 'in' expression
--     ;

      def "FromClause" $ record [
        "type">: optional $ csharp "Type",
        "identifier">: csharp "Identifier",
        "in">: csharp "Expression"],

-- query_body
--     : query_body_clauses? select_or_group_clause query_continuation?
--     ;

      def "QueryBody" $ record [
        "clauses">: list $ csharp "QueryBodyClause",
        "selectOrGroup">: csharp "SelectOrGroupClause",
        "continuation">: optional $ csharp "QueryContinuation"],

-- query_body_clauses
--     : query_body_clause
--     | query_body_clauses query_body_clause
--     ;
--
-- query_body_clause
--     : from_clause
--     | let_clause
--     | where_clause
--     | join_clause
--     | join_into_clause
--     | orderby_clause
--     ;

      def "QueryBodyClause" $ union [
        "from">: csharp "FromClause",
        "let">: csharp "LetClause",
        "where">: csharp "BooleanExpression",
        "join">: csharp "JoinClause",
        "orderby">: nonemptyList $ csharp "Ordering"],

-- let_clause
--     : 'let' identifier '=' expression
--     ;

      def "LetClause" $ record [
        "left">: csharp "Identifier",
        "right">: csharp "Expression"],

-- where_clause
--     : 'where' boolean_expression
--     ;
--
-- join_clause
--     : 'join' type? identifier 'in' expression 'on' expression
--       'equals' expression
--     ;

      def "JoinClause" $ record [
        "type">: optional $ csharp "Type",
        "identifier">: csharp "Identifier",
        "in">: csharp "Expression",
        "on">: csharp "Expression",
        "equals">: csharp "Expression",
        "into">: optional $ csharp "Identifier"],

-- join_into_clause
--     : 'join' type? identifier 'in' expression 'on' expression
--       'equals' expression 'into' identifier
--     ;
--
-- orderby_clause
--     : 'orderby' orderings
--     ;
--
-- orderings
--     : ordering (',' ordering)*
--     ;
--
-- ordering
--     : expression ordering_direction?
--     ;

      def "Ordering" $ record [
        "expression">: csharp "Expression",
        "direction">: optional $ csharp "OrderingDirection"],

-- ordering_direction
--     : 'ascending'
--     | 'descending'
--     ;

      def "OrderingDirection" $ enum [
        "ascending",
        "descending"],

-- select_or_group_clause
--     : select_clause
--     | group_clause
--     ;

      def "SelectOrGroupClause" $ union [
        "select">: csharp "Expression",
        "group">: csharp "GroupClause"],

-- select_clause
--     : 'select' expression
--     ;
--
-- group_clause
--     : 'group' expression 'by' expression
--     ;


      def "GroupClause" $ record [
        "grouped">: csharp "Expression",
        "by">: csharp "Expression"],

-- query_continuation
--     : 'into' identifier query_body
--     ;

      def "QueryContinuation" $ record [
        "into">: csharp "Identifier",
        "body">: csharp "QueryBody"],

-- // Source: §12.21.1 General
-- assignment
--     : unary_expression assignment_operator expression
--     ;

      def "Assignment" $ record [
        "left">: csharp "UnaryExpression",
        "operator">: csharp "AssignmentOperator",
        "right">: csharp "Expression"],

-- assignment_operator
--     : '=' 'ref'? | '+=' | '-=' | '*=' | '/=' | '%=' | '&=' | '|=' | '^=' | '<<='
--     | right_shift_assignment
--     ;

      def "AssignmentOperator" $ union [
        "simple">: boolean,
        "plusEquals">: unit,
        "minusEquals">: unit,
        "timesEquals">: unit,
        "divideEquals">: unit,
        "modEquals">: unit,
        "andEquals">: unit,
        "orEquals">: unit,
        "xorEquals">: unit,
        "leftShiftEquals">: unit,
        "rightShiftEquals">: unit],

-- // Source: §12.22 Expression
-- expression
--     : non_assignment_expression
--     | assignment
--     ;

      def "Expression" $ union [
        "nonAssignment">: csharp "NonAssignmentExpression",
        "assignment">: csharp "Assignment"],

-- non_assignment_expression
--     : declaration_expression
--     | conditional_expression
--     | lambda_expression
--     | query_expression
--     ;

      def "NonAssignmentExpression" $ union [
        "declaration">: csharp "DeclarationExpression",
        "conditional">: csharp "ConditionalExpression",
        "lambda">: csharp "LambdaExpression",
        "query">: csharp "QueryExpression"],

-- // Source: §12.23 Constant expressions
-- constant_expression
--     : expression
--     ;

      def "ConstantExpression" $ wrap $
        csharp "Expression",

-- // Source: §12.24 Boolean expressions
-- boolean_expression
--     : expression
--     ;

      def "BooleanExpression" $ wrap $
        csharp "Expression",

-- // Source: §13.1 General
-- statement
--     : labeled_statement
--     | declaration_statement
--     | embedded_statement
--     ;

      def "Statement" $ union [
        "labeled">: csharp "LabeledStatement",
        "declaration">: csharp "DeclarationStatement",
        "embedded">: csharp "EmbeddedStatement"],

-- embedded_statement
--     : block
--     | empty_statement
--     | expression_statement
--     | selection_statement
--     | iteration_statement
--     | jump_statement
--     | try_statement
--     | checked_statement
--     | unchecked_statement
--     | lock_statement
--     | using_statement
--     | yield_statement
--     | unsafe_statement   // unsafe code support
--     | fixed_statement    // unsafe code support
--     ;

      def "EmbeddedStatement" $ union [
        "block">: csharp "Block",
        "empty">: unit,
        "expression">: csharp "StatementExpression",
        "selection">: csharp "SelectionStatement",
        "iteration">: csharp "IterationStatement",
        "jump">: csharp "JumpStatement",
        "try">: csharp "TryStatement",
        "checked">: csharp "Block",
        "unchecked">: csharp "Block",
        "lock">: csharp "LockStatement",
        "using">: csharp "UsingStatement",
        "yield">: csharp "YieldStatement",
        "unsafe">: csharp "Block",
        "fixed">: csharp "FixedStatement"],

-- // Source: §13.3.1 General
-- block
--     : '{' statement_list? '}'
--     ;

      def "Block" $ wrap $
        list $ csharp "Statement",

-- // Source: §13.3.2 Statement lists
-- statement_list
--     : statement+
--     ;
--
-- // Source: §13.4 The empty statement
-- empty_statement
--     : ';'
--     ;
--
-- // Source: §13.5 Labeled statements
-- labeled_statement
--     : identifier ':' statement
--     ;

      def "LabeledStatement" $ record [
        "label">: csharp "Identifier",
        "statement">: csharp "Statement"],

-- // Source: §13.6.1 General
-- declaration_statement
--     : local_variable_declaration ';'
--     | local_constant_declaration ';'
--     | local_function_declaration
--     ;

      def "DeclarationStatement" $ union [
        "variable">: csharp "LocalVariableDeclaration",
        "constant">: csharp "LocalConstantDeclaration",
        "function">: csharp "LocalFunctionDeclaration"],

-- // Source: §13.6.2.1 General
-- local_variable_declaration
--     : implicitly_typed_local_variable_declaration
--     | explicitly_typed_local_variable_declaration
--     | ref_local_variable_declaration
--     ;


      def "LocalVariableDeclaration" $ union [
        "implicitlyTyped">: csharp "ImplicitlyTypedLocalVariableDeclaration",
        "explicitlyTyped">: csharp "ExplicitlyTypedLocalVariableDeclaration",
        "ref">: csharp "RefLocalVariableDeclaration"],

-- // Source: §13.6.2.2 Implicitly typed local variable declarations
-- implicitly_typed_local_variable_declaration
--     : 'var' implicitly_typed_local_variable_declarator
--     | ref_kind 'var' ref_local_variable_declarator
--     ;

      def "ImplicitlyTypedLocalVariableDeclaration" $ union [
        "var">: csharp "ImplicitlyTypedLocalVariableDeclarator",
        "refVar">: csharp "RefVarImplicitlyTypedLocalVariableDeclaration"],

      def "RefVarImplicitlyTypedLocalVariableDeclaration" $ record [
        "refKind">: csharp "RefKind",
        "declarator">: csharp "RefLocalVariableDeclarator"],

-- implicitly_typed_local_variable_declarator
--     : identifier '=' expression
--     ;

      def "ImplicitlyTypedLocalVariableDeclarator" $ record [
        "identifier">: csharp "Identifier",
        "expression">: csharp "Expression"],

-- // Source: §13.6.2.3 Explicitly typed local variable declarations
-- explicitly_typed_local_variable_declaration
--     : type explicitly_typed_local_variable_declarators
--     ;

      def "ExplicitlyTypedLocalVariableDeclaration" $ record [
        "type">: csharp "Type",
        "declarators">: list $ csharp "ExplicitlyTypedLocalVariableDeclarator"],

-- explicitly_typed_local_variable_declarators
--     : explicitly_typed_local_variable_declarator
--       (',' explicitly_typed_local_variable_declarator)*
--     ;

      def "ExplicitlyTypedLocalVariableDeclarator" $ record [
        "identifier">: csharp "Identifier",
        "initializer">: optional $ csharp "LocalVariableInitializer"],

-- explicitly_typed_local_variable_declarator
--     : identifier ('=' local_variable_initializer)?
--     ;
--
-- local_variable_initializer
--     : expression
--     | array_initializer
--     ;

      def "LocalVariableInitializer" $ union [
        "expression">: csharp "Expression",
        "initializer">: csharp "ArrayInitializer"],

-- // Source: §13.6.2.4 Ref local variable declarations
-- ref_local_variable_declaration
--     : ref_kind type ref_local_variable_declarators
--     ;

      def "RefLocalVariableDeclaration" $ record [
        "refKind">: csharp "RefKind",
        "type">: csharp "Type",
        "declarators">: nonemptyList $ csharp "RefLocalVariableDeclarator"],

-- ref_local_variable_declarators
--     : ref_local_variable_declarator (',' ref_local_variable_declarator)*
--     ;
--
-- ref_local_variable_declarator
--     : identifier '=' 'ref' variable_reference
--     ;

      def "RefLocalVariableDeclarator" $ record [
        "left">: csharp "Identifier",
        "right">: csharp "VariableReference"],

-- // Source: §13.6.3 Local constant declarations
-- local_constant_declaration
--     : 'const' type constant_declarators
--     ;

      def "LocalConstantDeclaration" $ record [
        "type">: csharp "Type",
        "declarators">: nonemptyList $ csharp "ConstantDeclarator"],

-- constant_declarators
--     : constant_declarator (',' constant_declarator)*
--     ;
--
-- constant_declarator
--     : identifier '=' constant_expression
--     ;

      def "ConstantDeclarator" $ record [
        "identifier">: csharp "Identifier",
        "expression">: csharp "ConstantExpression"],

-- // Source: §13.6.4 Local function declarations
-- local_function_declaration
--     : local_function_modifier* return_type local_function_header
--       local_function_body
--     | ref_local_function_modifier* ref_kind ref_return_type
--       local_function_header ref_local_function_body
--     ;

      def "LocalFunctionDeclaration" $ union [
        "standard">: csharp "StandardLocalFunctionDeclaration",
        "ref">: csharp "RefLocalFunctionDeclaration"],

      def "StandardLocalFunctionDeclaration" $ record [
        "modifiers">: list $ csharp "LocalFunctionModifier",
        "returnType">: csharp "ReturnType",
        "header">: csharp "LocalFunctionHeader",
        "body">: csharp "LocalFunctionBody"],

      def "RefLocalFunctionDeclaration" $ record [
        "modifiers">: list $ csharp "RefLocalFunctionModifier",
        "refKind">: csharp "RefKind",
        "returnType">: csharp "Type",
        "header">: csharp "LocalFunctionHeader",
        "body">: csharp "RefLocalFunctionBody"],

-- local_function_header
--     : identifier '(' formal_parameter_list? ')'
--     | identifier type_parameter_list '(' formal_parameter_list? ')'
--       type_parameter_constraints_clause*
--     ;

      def "LocalFunctionHeader" $ record [
        "identifier">: csharp "Identifier",
        "typeParameters">: optional $ csharp "TypeParameterList",
        "parameters">: csharp "FormalParameterList",
        "constraints">: list $ csharp "TypeParameterConstraintsClause"],

-- local_function_modifier
--     : ref_local_function_modifier
--     | 'async'
--     ;

      def "LocalFunctionModifier" $ union [
        "ref">: csharp "RefLocalFunctionModifier",
        "async">: unit],

-- ref_local_function_modifier
--     : 'static'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "RefLocalFunctionModifier" $ enum [
        "static",
        "unsafe"],

-- local_function_body
--     : block
--     | '=>' null_conditional_invocation_expression ';'
--     | '=>' expression ';'
--     ;

      def "LocalFunctionBody" $ union [
        "block">: csharp "Block",
        "nullConditionalInvocation">: csharp "NullConditionalInvocationExpression",
        "expression">: csharp "Expression"],

-- ref_local_function_body
--     : block
--     | '=>' 'ref' variable_reference ';'
--     ;

      def "RefLocalFunctionBody" $ union [
        "block">: csharp "Block",
        "ref">: csharp "VariableReference"],

-- // Source: §13.7 Expression statements
-- expression_statement
--     : statement_expression ';'
--     ;
--
-- statement_expression
--     : null_conditional_invocation_expression
--     | invocation_expression
--     | object_creation_expression
--     | assignment
--     | post_increment_expression
--     | post_decrement_expression
--     | pre_increment_expression
--     | pre_decrement_expression
--     | await_expression
--     ;

      def "StatementExpression" $ union [
        "nullConditionalInvocation">: csharp "NullConditionalInvocationExpression",
        "invocation">: csharp "InvocationExpression",
        "objectCreation">: csharp "ObjectCreationExpression",
        "assignment">: csharp "Assignment",
        "postIncrement">: csharp "PrimaryExpression",
        "postDecrement">: csharp "PrimaryExpression",
        "preIncrement">: csharp "UnaryExpression",
        "preDecrement">: csharp "UnaryExpression",
        "await">: csharp "UnaryExpression"],

-- // Source: §13.8.1 General
-- selection_statement
--     : if_statement
--     | switch_statement
--     ;

      def "SelectionStatement" $ union [
        "if">: csharp "IfStatement",
        "switch">: csharp "SwitchStatement"],

-- // Source: §13.8.2 The if statement
-- if_statement
--     : 'if' '(' boolean_expression ')' embedded_statement
--     | 'if' '(' boolean_expression ')' embedded_statement
--       'else' embedded_statement
--     ;

      def "IfStatement" $ record [
        "condition">: csharp "BooleanExpression",
        "ifBranch">: csharp "EmbeddedStatement",
        "elseBranch">: csharp "EmbeddedStatement"],

-- // Source: §13.8.3 The switch statement
-- switch_statement
--     : 'switch' '(' expression ')' switch_block
--     ;

      def "SwitchStatement" $ record [
        "expression">: csharp "Expression",
        "branches">: list $ csharp "SwitchSection"],

-- switch_block
--     : '{' switch_section* '}'
--     ;
--
-- switch_section
--     : switch_label+ statement_list
--     ;

      def "SwitchSection" $ record [
        "labels">: nonemptyList $ csharp "SwitchLabel",
        "statements">: list $ csharp "Statement"],

-- switch_label
--     : 'case' pattern case_guard?  ':'
--     | 'default' ':'
--     ;

      def "SwitchLabel" $ union [
        "branch">: csharp "SwitchBranch",
        "default">: unit],

      def "SwitchBranch" $ record [
        "pattern">: csharp "Pattern",
        "guard">: optional $ csharp "Expression"],

-- case_guard
--     : 'when' expression
--     ;
--
-- // Source: §13.9.1 General
-- iteration_statement
--     : while_statement
--     | do_statement
--     | for_statement
--     | foreach_statement
--     ;

      def "IterationStatement" $ union [
        "while">: csharp "WhileStatement",
        "do">: csharp "DoStatement",
        "for">: csharp "ForStatement",
        "foreach">: csharp "ForeachStatement"],

-- // Source: §13.9.2 The while statement
-- while_statement
--     : 'while' '(' boolean_expression ')' embedded_statement
--     ;

      def "WhileStatement" $ record [
        "condition">: csharp "BooleanExpression",
        "body">: csharp "EmbeddedStatement"],

-- // Source: §13.9.3 The do statement
-- do_statement
--     : 'do' embedded_statement 'while' '(' boolean_expression ')' ';'
--     ;

      def "DoStatement" $ record [
        "body">: csharp "EmbeddedStatement",
        "while">: csharp "BooleanExpression"],

-- // Source: §13.9.4 The for statement
-- for_statement
--     : 'for' '(' for_initializer? ';' for_condition? ';' for_iterator? ')'
--       embedded_statement
--     ;

        def "ForStatement" $ record [
          "initializer">: optional $ csharp "ForInitializer",
          "condition">: optional $ csharp "BooleanExpression",
          "iterator">: optional $ csharp "StatementExpressionList",
          "body">: csharp "EmbeddedStatement"],

-- for_initializer
--     : local_variable_declaration
--     | statement_expression_list
--     ;

      def "ForInitializer" $ union [
        "variable">: csharp "LocalVariableDeclaration",
        "statements">: csharp "StatementExpressionList"],

-- for_condition
--     : boolean_expression
--     ;
--
-- for_iterator
--     : statement_expression_list
--     ;
--
-- statement_expression_list
--     : statement_expression (',' statement_expression)*
--     ;

      def "StatementExpressionList" $ nonemptyList $ csharp "StatementExpression",

-- // Source: §13.9.5 The foreach statement
-- foreach_statement
--     : 'foreach' '(' ref_kind? local_variable_type identifier 'in'
--       expression ')' embedded_statement
--     ;

      def "ForeachStatement" $ record [
        "kind">: optional $ csharp "RefKind",
        "type">: csharp "LocalVariableType",
        "identifier">: csharp "Identifier",
        "expression">: csharp "Expression",
        "body">: csharp "EmbeddedStatement"],

-- // Source: §13.10.1 General
-- jump_statement
--     : break_statement
--     | continue_statement
--     | goto_statement
--     | return_statement
--     | throw_statement
--     ;

      def "JumpStatement" $ union [
        "break">: unit,
        "continue">: unit,
        "goto">: csharp "GotoStatement",
        "return">: csharp "ReturnStatement",
        "throw">: optional $ csharp "Expression"],

-- // Source: §13.10.2 The break statement
-- break_statement
--     : 'break' ';'
--     ;
--
-- // Source: §13.10.3 The continue statement
-- continue_statement
--     : 'continue' ';'
--     ;
--
-- // Source: §13.10.4 The goto statement
-- goto_statement
--     : 'goto' identifier ';'
--     | 'goto' 'case' constant_expression ';'
--     | 'goto' 'default' ';'
--     ;

      def "GotoStatement" $ union [
        "identifier">: csharp "Identifier",
        "case">: csharp "ConstantExpression",
        "default">: unit],

-- // Source: §13.10.5 The return statement
-- return_statement
--     : 'return' ';'
--     | 'return' expression ';'
--     | 'return' 'ref' variable_reference ';'
--     ;

      def "ReturnStatement" $ union [
        "simple">: unit,
        "value">: csharp "Expression",
        "ref">: csharp "VariableReference"],

-- // Source: §13.10.6 The throw statement
-- throw_statement
--     : 'throw' expression? ';'
--     ;
--
-- // Source: §13.11 The try statement
-- try_statement
--     : 'try' block catch_clauses
--     | 'try' block catch_clauses? finally_clause
--     ;

      def "TryStatement" $ record [
        "body">: csharp "Block",
        "catches">: csharp "CatchClauses",
        "finally">: optional $ csharp "Block"],

-- catch_clauses
--     : specific_catch_clause+
--     | specific_catch_clause* general_catch_clause
--     ;

      def "CatchClauses" $ union [
        "specific">: list $ csharp "SpecificCatchClause",
        "general">: csharp "Block"],

-- specific_catch_clause
--     : 'catch' exception_specifier exception_filter? block
--     | 'catch' exception_filter block
--     ;

      def "SpecificCatchClause" $ record [
        "specifier">: optional $ csharp "ExceptionSpecifier",
        "filter">: optional $ csharp "BooleanExpression",
        "body">: csharp "Block"],

-- exception_specifier
--     : '(' type identifier? ')'
--     ;

      def "ExceptionSpecifier" $ record [
        "type">: csharp "Type",
        "identifier">: optional $ csharp "Identifier"],

-- exception_filter
--     : 'when' '(' boolean_expression ')'
--     ;
--
-- general_catch_clause
--     : 'catch' block
--     ;
--
-- finally_clause
--     : 'finally' block
--     ;
--
-- // Source: §13.12 The checked and unchecked statements
-- checked_statement
--     : 'checked' block
--     ;
--
-- unchecked_statement
--     : 'unchecked' block
--     ;
--
-- // Source: §13.13 The lock statement
-- lock_statement
--     : 'lock' '(' expression ')' embedded_statement
--     ;

      def "LockStatement" $ record [
        "expression">: csharp "Expression",
        "body">: csharp "EmbeddedStatement"],

-- // Source: §13.14 The using statement
-- using_statement
--     : 'using' '(' resource_acquisition ')' embedded_statement
--     ;

      def "UsingStatement" $ record [
        "acquisition">: csharp "ResourceAcquisition",
        "body">: csharp "EmbeddedStatement"],

-- resource_acquisition
--     : local_variable_declaration
--     | expression
--     ;

      def "ResourceAcquisition" $ union [
        "local">: csharp "LocalVariableDeclaration",
        "expression">: csharp "Expression"],

-- // Source: §13.15 The yield statement
-- yield_statement
--     : 'yield' 'return' expression ';'
--     | 'yield' 'break' ';'
--     ;

      def "YieldStatement" $ union [
        "return">: csharp "Expression",
        "break">: unit],

-- // Source: §14.2 Compilation units
-- compilation_unit
--     : extern_alias_directive* using_directive* global_attributes?
--       namespace_member_declaration*
--     ;

      def "CompilationUnit" $ record [
        "externs">: list $ csharp "ExternAliasDirective",
        "usings">: list $ csharp "UsingDirective",
        "attributes">: list $ csharp "GlobalAttributeSection",
        "members">: list $ csharp "NamespaceMemberDeclaration"],

-- // Source: §14.3 Namespace declarations
-- namespace_declaration
--     : 'namespace' qualified_identifier namespace_body ';'?
--     ;

      def "NamespaceDeclaration" $ record [
        "name">: nonemptyList $ csharp "Identifier",
        "body">: csharp "NamespaceBody"],

-- qualified_identifier
--     : identifier ('.' identifier)*
--     ;
--
-- namespace_body
--     : '{' extern_alias_directive* using_directive*
--       namespace_member_declaration* '}'
--     ;

      def "NamespaceBody" $ record [
        "externs">: list $ csharp "ExternAliasDirective",
        "usings">: list $ csharp "UsingDirective",
        "members">: list $ csharp "NamespaceMemberDeclaration"],

-- // Source: §14.4 Extern alias directives
-- extern_alias_directive
--     : 'extern' 'alias' identifier ';'
--     ;

      def "ExternAliasDirective" $ wrap $
        csharp "Identifier",

-- // Source: §14.5.1 General
-- using_directive
--     : using_alias_directive
--     | using_namespace_directive
--     | using_static_directive
--     ;

      def "UsingDirective" $ union [
        "alias">: csharp "UsingAliasDirective",
        "namespace">: csharp "NamespaceName",
        "static">: csharp "TypeName"],

-- // Source: §14.5.2 Using alias directives
-- using_alias_directive
--     : 'using' identifier '=' namespace_or_type_name ';'
--     ;

      def "UsingAliasDirective" $ record [
        "alias">: csharp "Identifier",
        "name">: csharp "NamespaceOrTypeName"],

-- // Source: §14.5.3 Using namespace directives
-- using_namespace_directive
--     : 'using' namespace_name ';'
--     ;
--
-- // Source: §14.5.4 Using static directives
-- using_static_directive
--     : 'using' 'static' type_name ';'
--     ;
--
-- // Source: §14.6 Namespace member declarations
-- namespace_member_declaration
--     : namespace_declaration
--     | type_declaration
--     ;

      def "NamespaceMemberDeclaration" $ union [
        "namespace">: csharp "NamespaceDeclaration",
        "type">: csharp "TypeDeclaration"],

-- // Source: §14.7 Type declarations
-- type_declaration
--     : class_declaration
--     | struct_declaration
--     | interface_declaration
--     | enum_declaration
--     | delegate_declaration
--     ;

      def "TypeDeclaration" $ union [
        "class">: csharp "ClassDeclaration",
        "struct">: csharp "StructDeclaration",
        "interface">: csharp "InterfaceDeclaration",
        "enum">: csharp "EnumDeclaration",
        "delegate">: csharp "DelegateDeclaration"],

-- // Source: §14.8.1 General
-- qualified_alias_member
--     : identifier '::' identifier type_argument_list?
--     ;

      def "QualifiedAliasMember" $ record [
        "alias">: csharp "Identifier",
        "member">: csharp "Identifier",
        "arguments">: optional $ csharp "TypeArgumentList"],

-- // Source: §15.2.1 General
-- class_declaration
--     : attributes? class_modifier* 'partial'? 'class' identifier
--         type_parameter_list? class_base? type_parameter_constraints_clause*
--         class_body ';'?
--     ;

      def "ClassDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "ClassModifier",
        "partial">: unit,
        "name">: csharp "Identifier",
        "parameters">: optional $ csharp "TypeParameterList",
        "base">: optional $ csharp "ClassBase",
        "constraints">: list $ csharp "TypeParameterConstraintsClause",
        "body">: csharp "ClassBody"],

-- // Source: §15.2.2.1 General
-- class_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | 'abstract'
--     | 'sealed'
--     | 'static'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "ClassModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private",
        "abstract",
        "sealed",
        "static",
        "unsafe"],

-- // Source: §15.2.3 Type parameters
-- type_parameter_list
--     : '<' type_parameters '>'
--     ;
--
-- type_parameters
--     : attributes? type_parameter
--     | type_parameters ',' attributes? type_parameter
--     ;

      def "TypeParameterList" $ nonemptyList $ csharp "TypeParameterPart",

      def "TypeParameterPart" $ record [
        "attributes">: optional $ csharp "Attributes",
        "name">: csharp "TypeParameter"],

-- // Source: §15.2.4.1 General
-- class_base
--     : ':' class_type
--     | ':' interface_type_list
--     | ':' class_type ',' interface_type_list
--     ;

      def "ClassBase" $ union [
        "class">: optional $ csharp "ClassType",
        "interfaces">: list $ csharp "InterfaceType"],

-- interface_type_list
--     : interface_type (',' interface_type)*
--     ;
--
-- // Source: §15.2.5 Type parameter constraints
-- type_parameter_constraints_clauses
--     : type_parameter_constraints_clause
--     | type_parameter_constraints_clauses type_parameter_constraints_clause
--     ;
--
-- type_parameter_constraints_clause
--     : 'where' type_parameter ':' type_parameter_constraints
--     ;

      def "TypeParameterConstraintsClause" $ record [
        "parameter">: csharp "TypeParameter",
        "constraints">: list $ csharp "TypeParameterConstraints"],

-- type_parameter_constraints
--     : primary_constraint
--     | secondary_constraints
--     | constructor_constraint
--     | primary_constraint ',' secondary_constraints
--     | primary_constraint ',' constructor_constraint
--     | secondary_constraints ',' constructor_constraint
--     | primary_constraint ',' secondary_constraints ',' constructor_constraint
--     ;

      def "TypeParameterConstraints" $ record [
        "primary">: optional $ csharp "PrimaryConstraint",
        "secondary">: optional $ csharp "SecondaryConstraints",
        "constructor">: boolean],

-- primary_constraint
--     : class_type
--     | 'class'
--     | 'struct'
--     | 'unmanaged'
--     ;

      def "PrimaryConstraint" $ union [
        "classType">: csharp "ClassType",
        "class">: unit,
        "struct">: unit,
        "unmanaged">: unit],

-- secondary_constraints
--     : interface_type
--     | type_parameter
--     | secondary_constraints ',' interface_type
--     | secondary_constraints ',' type_parameter
--     ;

      def "SecondaryConstraints" $ nonemptyList $ csharp "SecondaryConstraint",

      def "SecondaryConstraint" $ union [
        "interface">: csharp "InterfaceType",
        "parameter">: csharp "TypeParameter"],

-- constructor_constraint
--     : 'new' '(' ')'
--     ;
--
-- // Source: §15.2.6 Class body
-- class_body
--     : '{' class_member_declaration* '}'
--     ;

      def "ClassBody" $ wrap $
        list $ csharp "ClassMemberDeclaration",

-- // Source: §15.3.1 General
-- class_member_declaration
--     : constant_declaration
--     | field_declaration
--     | method_declaration
--     | property_declaration
--     | event_declaration
--     | indexer_declaration
--     | operator_declaration
--     | constructor_declaration
--     | finalizer_declaration
--     | static_constructor_declaration
--     | type_declaration
--     ;

      def "ClassMemberDeclaration" $ union [
        "constant">: csharp "ConstantDeclaration",
        "field">: csharp "FieldDeclaration",
        "method">: csharp "MethodDeclaration",
        "property">: csharp "PropertyDeclaration",
        "event">: csharp "EventDeclaration",
        "indexer">: csharp "IndexerDeclaration",
        "operator">: csharp "OperatorDeclaration",
        "constructor">: csharp "ConstructorDeclaration",
        "finalizer">: csharp "FinalizerDeclaration",
        "staticConstructor">: csharp "StaticConstructorDeclaration",
        "type">: csharp "TypeDeclaration"],

-- // Source: §15.4 Constants
-- constant_declaration
--     : attributes? constant_modifier* 'const' type constant_declarators ';'
--     ;

      def "ConstantDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "ConstantModifier",
        "type">: csharp "Type",
        "declarators">: nonemptyList $ csharp "ConstantDeclarator"],

-- constant_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     ;

      def "ConstantModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private"],

-- // Source: §15.5.1 General
-- field_declaration
--     : attributes? field_modifier* type variable_declarators ';'
--     ;

      def "FieldDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "FieldModifier",
        "type">: csharp "Type",
        "declarators">: nonemptyList $ csharp "VariableDeclarator"],

-- field_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | 'static'
--     | 'readonly'
--     | 'volatile'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "FieldModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private",
        "static",
        "readonly",
        "volatile",
        "unsafe"],

-- variable_declarators
--     : variable_declarator (',' variable_declarator)*
--     ;

      def "VariableDeclarators" $ nonemptyList $ csharp "VariableDeclarator",

-- variable_declarator
--     : identifier ('=' variable_initializer)?
--     ;

      def "VariableDeclarator" $ record [
        "identifier">: csharp "Identifier",
        "initializer">: optional $ csharp "VariableInitializer"],

-- // Source: §15.6.1 General
-- method_declaration
--     : attributes? method_modifiers return_type method_header method_body
--     | attributes? ref_method_modifiers ref_kind ref_return_type method_header
--       ref_method_body
--     ;

      def "MethodDeclaration" $ union [
        "standard">: csharp "StandardMethodDeclaration",
        "refReturn">: csharp "RefReturnMethodDeclaration"],

      def "StandardMethodDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "MethodModifier",
        "returnType">: csharp "ReturnType",
        "header">: csharp "MethodHeader",
        "body">: csharp "MethodBody"],

      def "RefReturnMethodDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "RefMethodModifier",
        "kind">: csharp "RefKind",
        "returnType">: csharp "ReturnType",
        "header">: csharp "MethodHeader",
        "body">: csharp "RefMethodBody"],

-- method_modifiers
--     : method_modifier* 'partial'?
--     ;

      def "MethodModifiers" $ record [
        "modifiers">: list $ csharp "MethodModifier",
        "partial">: boolean],

-- ref_kind
--     : 'ref'
--     | 'ref' 'readonly'
--     ;

      def "RefKind" $ enum [
        "ref",
        "refReadonly"],

-- ref_method_modifiers
--     : ref_method_modifier*
--     ;
--
-- method_header
--     : member_name '(' formal_parameter_list? ')'
--     | member_name type_parameter_list '(' formal_parameter_list? ')'
--       type_parameter_constraints_clause*
--     ;

      def "MethodHeader" $ record [
        "name">: csharp "MemberName",
        "typeParameters">: optional $ csharp "TypeParameterList",
        "parameters">: optional $ csharp "FormalParameterList",
        "constraints">: list $ csharp "TypeParameterConstraintsClause"],

-- method_modifier
--     : ref_method_modifier
--     | 'async'
--     ;

      def "MethodModifier" $ union [
        "ref">: csharp "RefMethodModifier",
        "async">: unit],

-- ref_method_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | 'static'
--     | 'virtual'
--     | 'sealed'
--     | 'override'
--     | 'abstract'
--     | 'extern'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "RefMethodModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private",
        "static",
        "virtual",
        "sealed",
        "override",
        "abstract",
        "extern",
        "unsafe"],

-- return_type
--     : ref_return_type
--     | 'void'
--     ;

      def "ReturnType" $ union [
        "ref">: csharp "Type",
        "void">: unit],

-- ref_return_type
--     : type
--     ;
--
-- member_name
--     : identifier
--     | interface_type '.' identifier
--     ;

      def "MemberName" $ record [
        "interfaceType">: optional $ csharp "TypeName",
        "identifier">: csharp "Identifier"],

-- method_body
--     : block
--     | '=>' null_conditional_invocation_expression ';'
--     | '=>' expression ';'
--     | ';'
--     ;

      def "MethodBody" $ union [
        "block">: csharp "Block",
        "nullConditionalInvocation">: csharp "NullConditionalInvocationExpression",
        "expression">: csharp "Expression",
        "empty">: unit],

-- ref_method_body
--     : block
--     | '=>' 'ref' variable_reference ';'
--     | ';'
--     ;

      def "RefMethodBody" $ union [
        "block">: csharp "Block",
        "ref">: csharp "VariableReference",
        "empty">: unit],

-- // Source: §15.6.2.1 General
-- formal_parameter_list
--     : fixed_parameters
--     | fixed_parameters ',' parameter_array
--     | parameter_array
--     ;

      def "FormalParameterList" $ record [
        "fixed">: list $ csharp "FixedParameter",
        "array">: optional $ csharp "ParameterArray"],

-- fixed_parameters
--     : fixed_parameter (',' fixed_parameter)*
--     ;
--
-- fixed_parameter
--     : attributes? parameter_modifier? type identifier default_argument?
--     ;

      def "FixedParameter" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifier">: optional $ csharp "ParameterModifier",
        "type">: csharp "Type",
        "identifier">: csharp "Identifier",
        "defaultArgument">: optional $ csharp "Expression"],

-- default_argument
--     : '=' expression
--     ;
--
-- parameter_modifier
--     : parameter_mode_modifier
--     | 'this'
--     ;

      def "ParameterModifier" $ union [
        "mode">: csharp "ParameterModeModifier",
        "this">: unit],

-- parameter_mode_modifier
--     : 'ref'
--     | 'out'
--     | 'in'
--     ;

      def "ParameterModeModifier" $ enum [
        "ref",
        "out",
        "in"],

-- parameter_array
--     : attributes? 'params' array_type identifier
--     ;

      def "ParameterArray" $ record [
        "attributes">: optional $ csharp "Attributes",
        "type">: csharp "ArrayType",
        "identifier">: csharp "Identifier"],

-- // Source: §15.7.1 General
-- property_declaration
--     : attributes? property_modifier* type member_name property_body
--     | attributes? property_modifier* ref_kind type member_name ref_property_body
--     ;

      def "PropertyDeclaration" $ union [
        "standard">: csharp "StandardPropertyDeclaration",
        "refReturn">: csharp "RefReturnPropertyDeclaration"],

      def "StandardPropertyDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "PropertyModifier",
        "type">: csharp "Type",
        "name">: csharp "MemberName",
        "body">: csharp "PropertyBody"],

      def "RefReturnPropertyDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "PropertyModifier",
        "refKind">: csharp "RefKind",
        "type">: csharp "Type",
        "name">: csharp "MemberName",
        "body">: csharp "RefPropertyBody"],

-- property_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | 'static'
--     | 'virtual'
--     | 'sealed'
--     | 'override'
--     | 'abstract'
--     | 'extern'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "PropertyModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private",
        "static",
        "virtual",
        "sealed",
        "override",
        "abstract",
        "extern",
        "unsafe"],

-- property_body
--     : '{' accessor_declarations '}' property_initializer?
--     | '=>' expression ';'
--     ;

      def "PropertyBody" $ union [
        "block">: csharp "BlockPropertyBody",
        "expression">: csharp "Expression"],

      def "BlockPropertyBody" $ record [
        "accessors">: csharp "AccessorDeclarations",
        "initializer">: optional $ csharp "VariableInitializer"],

-- property_initializer
--     : '=' variable_initializer ';'
--     ;
--
-- ref_property_body
--     : '{' ref_get_accessor_declaration '}'
--     | '=>' 'ref' variable_reference ';'
--     ;

      def "RefPropertyBody" $ union [
        "block">: csharp "RefGetAccessorDeclaration",
        "ref">: csharp "VariableReference"],

-- // Source: §15.7.3 Accessors
-- accessor_declarations
--     : get_accessor_declaration set_accessor_declaration?
--     | set_accessor_declaration get_accessor_declaration?
--     ;

      def "AccessorDeclarations" $ union [
        "get">: optional $ csharp "AccessorDeclaration",
        "set">: optional $ csharp "AccessorDeclaration"],

      def "AccessorDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifier">: optional $ csharp "AccessorModifier",
        "body">: csharp "AccessorBody"],

-- get_accessor_declaration
--     : attributes? accessor_modifier? 'get' accessor_body
--     ;
--
-- set_accessor_declaration
--     : attributes? accessor_modifier? 'set' accessor_body
--     ;
--
-- accessor_modifier
--     : 'protected'
--     | 'internal'
--     | 'private'
--     | 'protected' 'internal'
--     | 'internal' 'protected'
--     | 'protected' 'private'
--     | 'private' 'protected'
--     ;

      def "AccessorModifier" $ enum [
        "protected",
        "internal",
        "private",
        "protectedInternal",
        "internalProtected",
        "protectedPrivate",
        "privateProtected"],

-- accessor_body
--     : block
--     | '=>' expression ';'
--     | ';'
--     ;

      def "AccessorBody" $ union [
        "block">: csharp "Block",
        "expression">: csharp "Expression",
        "empty">: unit],

-- ref_get_accessor_declaration
--     : attributes? accessor_modifier? 'get' ref_accessor_body
--     ;

      def "RefGetAccessorDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifier">: optional $ csharp "AccessorModifier",
        "body">: csharp "RefAccessorBody"],

-- ref_accessor_body
--     : block
--     | '=>' 'ref' variable_reference ';'
--     | ';'
--     ;

      def "RefAccessorBody" $ union [
        "block">: csharp "Block",
        "ref">: csharp "VariableReference",
        "empty">: unit],

-- // Source: §15.8.1 General
-- event_declaration
--     : attributes? event_modifier* 'event' type variable_declarators ';'
--     | attributes? event_modifier* 'event' type member_name
--         '{' event_accessor_declarations '}'
--     ;

      def "EventDeclaration" $ union [
        "standard">: csharp "StandardEventDeclaration",
        "accessors">: csharp "AccessorsEventDeclaration"],

      def "StandardEventDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "EventModifier",
        "type">: csharp "Type",
        "declarators">: csharp "VariableDeclarators"],

      def "AccessorsEventDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "EventModifier",
        "type">: csharp "Type",
        "name">: csharp "MemberName",
        "accessors">: csharp "EventAccessorDeclarations"],

-- event_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | 'static'
--     | 'virtual'
--     | 'sealed'
--     | 'override'
--     | 'abstract'
--     | 'extern'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "EventModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private",
        "static",
        "virtual",
        "sealed",
        "override",
        "abstract",
        "extern",
        "unsafe"],

-- event_accessor_declarations
--     : add_accessor_declaration remove_accessor_declaration
--     | remove_accessor_declaration add_accessor_declaration
--     ;

      def "EventAccessorDeclarations" $ union [
        "add">: csharp "AddRemoveAccessorDeclaration",
        "remove">: csharp "AddRemoveAccessorDeclaration"],

      def "AddRemoveAccessorDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "body">: csharp "Block"],

-- add_accessor_declaration
--     : attributes? 'add' block
--     ;
--
-- remove_accessor_declaration
--     : attributes? 'remove' block
--     ;
--
-- // Source: §15.9.1 General
-- indexer_declaration
--     : attributes? indexer_modifier* indexer_declarator indexer_body
--     | attributes? indexer_modifier* ref_kind indexer_declarator ref_indexer_body
--     ;

      def "IndexerDeclaration" $ union [
        "standard">: csharp "StandardIndexerDeclaration",
        "ref">: csharp "RefIndexerDeclaration"],

      def "StandardIndexerDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "IndexerModifier",
        "declarator">: csharp "IndexerDeclarator",
        "body">: csharp "IndexerBody"],

      def "RefIndexerDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "IndexerModifier",
        "refKind">: csharp "RefKind",
        "declarator">: csharp "IndexerDeclarator",
        "body">: csharp "RefIndexerBody"],

-- indexer_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | 'virtual'
--     | 'sealed'
--     | 'override'
--     | 'abstract'
--     | 'extern'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "IndexerModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private",
        "virtual",
        "sealed",
        "override",
        "abstract",
        "extern",
        "unsafe"],

-- indexer_declarator
--     : type 'this' '[' formal_parameter_list ']'
--     | type interface_type '.' 'this' '[' formal_parameter_list ']'
--     ;

      def "IndexerDeclarator" $ record [
        "type">: csharp "Type",
        "interface">: optional $ csharp "InterfaceType",
        "parameters">: csharp "FormalParameterList"],

-- indexer_body
--     : '{' accessor_declarations '}'
--     | '=>' expression ';'
--     ;

      def "IndexerBody" $ union [
        "block">: csharp "AccessorDeclarations",
        "expression">: csharp "Expression"],

-- ref_indexer_body
--     : '{' ref_get_accessor_declaration '}'
--     | '=>' 'ref' variable_reference ';'
--     ;

      def "RefIndexerBody" $ union [
        "block">: csharp "RefGetAccessorDeclaration",
        "ref">: csharp "VariableReference"],

-- // Source: §15.10.1 General
-- operator_declaration
--     : attributes? operator_modifier+ operator_declarator operator_body
--     ;

      def "OperatorDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "OperatorModifier",
        "declarator">: csharp "OperatorDeclarator",
        "body">: csharp "OperatorBody"],

-- operator_modifier
--     : 'public'
--     | 'static'
--     | 'extern'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "OperatorModifier" $ enum [
        "public",
        "static",
        "extern",
        "unsafe"],

-- operator_declarator
--     : unary_operator_declarator
--     | binary_operator_declarator
--     | conversion_operator_declarator
--     ;

      def "OperatorDeclarator" $ union [
        "unary">: csharp "UnaryOperatorDeclarator",
        "binary">: csharp "BinaryOperatorDeclarator",
        "conversion">: csharp "ConversionOperatorDeclarator"],

-- unary_operator_declarator
--     : type 'operator' overloadable_unary_operator '(' fixed_parameter ')'
--     ;

      def "UnaryOperatorDeclarator" $ record [
        "type">: csharp "Type",
        "operator">: csharp "OverloadableUnaryOperator",
        "parameter">: csharp "FixedParameter"],

-- overloadable_unary_operator
--     : '+' | '-' | '!' | '~' | '++' | '--' | 'true' | 'false'
--     ;

      def "OverloadableUnaryOperator" $ enum [
        "plus",
        "minus",
        "not",
        "complement",
        "increment",
        "decrement",
        "true",
        "false"],

-- binary_operator_declarator
--     : type 'operator' overloadable_binary_operator
--         '(' fixed_parameter ',' fixed_parameter ')'
--     ;

      def "BinaryOperatorDeclarator" $ record [
        "type">: csharp "Type",
        "operator">: csharp "OverloadableBinaryOperator",
        "left">: csharp "FixedParameter",
        "right">: csharp "FixedParameter"],

-- overloadable_binary_operator
--     : '+'  | '-'  | '*'  | '/'  | '%'  | '&' | '|' | '^'  | '<<'
--     | right_shift | '==' | '!=' | '>' | '<' | '>=' | '<='
--     ;

      def "OverloadableBinaryOperator" $ enum [
        "add",
        "subtract",
        "multiply",
        "divide",
        "modulus",
        "and",
        "or",
        "xor",
        "leftShift",
        "rightShift",
        "equal",
        "notEqual",
        "greaterThan",
        "lessThan",
        "greaterThanOrEqual",
        "lessThanOrEqual"],

-- conversion_operator_declarator
--     : 'implicit' 'operator' type '(' fixed_parameter ')'
--     | 'explicit' 'operator' type '(' fixed_parameter ')'
--     ;

      def "ConversionOperatorDeclarator" $ record [
        "kind">: csharp "ConversionKind",
        "type">: csharp "Type",
        "parameter">: csharp "FixedParameter"],

      def "ConversionKind" $ enum [
        "implicit",
        "explicit"],

-- operator_body
--     : block
--     | '=>' expression ';'
--     | ';'
--     ;

      def "OperatorBody" $ union [
        "block">: csharp "Block",
        "expression">: csharp "Expression",
        "empty">: unit],

-- // Source: §15.11.1 General
-- constructor_declaration
--     : attributes? constructor_modifier* constructor_declarator constructor_body
--     ;

      def "ConstructorDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "ConstructorModifier",
        "declarator">: csharp "ConstructorDeclarator",
        "body">: csharp "ConstructorBody"],

-- constructor_modifier
--     : 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | 'extern'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "ConstructorModifier" $ enum [
        "public",
        "protected",
        "internal",
        "private",
        "extern",
        "unsafe"],

-- constructor_declarator
--     : identifier '(' formal_parameter_list? ')' constructor_initializer?
--     ;

      def "ConstructorDeclarator" $ record [
        "name">: csharp "Identifier",
        "parameters">: optional $ csharp "FormalParameterList",
        "initializer">: optional $ csharp "ConstructorInitializer"],

-- constructor_initializer
--     : ':' 'base' '(' argument_list? ')'
--     | ':' 'this' '(' argument_list? ')'
--     ;

      def "ConstructorInitializer" $ union [
        "base">: optional $ csharp "ArgumentList",
        "this">: optional $ csharp "ArgumentList"],

-- constructor_body
--     : block
--     | '=>' expression ';'
--     | ';'
--     ;

      def "ConstructorBody" $ union [
        "block">: csharp "Block",
        "expression">: csharp "Expression",
        "empty">: unit],

-- // Source: §15.12 Static constructors
-- static_constructor_declaration
--     : attributes? static_constructor_modifiers identifier '(' ')'
--         static_constructor_body
--     ;

      def "StaticConstructorDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: csharp "StaticConstructorModifiers",
        "name">: csharp "Identifier",
        "body">: csharp "StaticConstructorBody"],

-- static_constructor_modifiers
--     : 'static'
--     | 'static' 'extern' unsafe_modifier?
--     | 'static' unsafe_modifier 'extern'?
--     | 'extern' 'static' unsafe_modifier?
--     | 'extern' unsafe_modifier 'static'
--     | unsafe_modifier 'static' 'extern'?
--     | unsafe_modifier 'extern' 'static'
--     ;

      def "StaticConstructorModifiers" $ record [
        "extern">: boolean,
        "unsafe">: boolean],

-- static_constructor_body
--     : block
--     | '=>' expression ';'
--     | ';'
--     ;

      def "StaticConstructorBody" $ union [
        "block">: csharp "Block",
        "expression">: csharp "Expression",
        "empty">: unit],

-- // Source: §15.13 Finalizers
-- finalizer_declaration
--     : attributes? '~' identifier '(' ')' finalizer_body
--     | attributes? 'extern' unsafe_modifier? '~' identifier '(' ')'
--       finalizer_body
--     | attributes? unsafe_modifier 'extern'? '~' identifier '(' ')'
--       finalizer_body
--     ;

      def "FinalizerDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "extern">: boolean,
        "unsafe">: boolean,
        "name">: csharp "Identifier",
        "body">: csharp "FinalizerBody"],

-- finalizer_body
--     : block
--     | '=>' expression ';'
--     | ';'
--     ;

      def "FinalizerBody" $ union [
        "block">: csharp "Block",
        "expression">: csharp "Expression",
        "empty">: unit],

-- // Source: §16.2.1 General
-- struct_declaration
--     : attributes? struct_modifier* 'ref'? 'partial'? 'struct'
--       identifier type_parameter_list? struct_interfaces?
--       type_parameter_constraints_clause* struct_body ';'?
--     ;

      def "StructDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "StructModifier",
        "ref">: boolean,
        "partial">: boolean,
        "name">: csharp "Identifier",
        "parameters">: optional $ csharp "TypeParameterList",
        "interfaces">: list $ csharp "InterfaceType",
        "constraints">: list $ csharp "TypeParameterConstraintsClause",
        "body">: list $ csharp "StructMemberDeclaration"],

-- // Source: §16.2.2 Struct modifiers
-- struct_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | 'readonly'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "StructModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private",
        "readonly",
        "unsafe"],

-- // Source: §16.2.5 Struct interfaces
-- struct_interfaces
--     : ':' interface_type_list
--     ;
--
-- // Source: §16.2.6 Struct body
-- struct_body
--     : '{' struct_member_declaration* '}'
--     ;
--
-- // Source: §16.3 Struct members
-- struct_member_declaration
--     : constant_declaration
--     | field_declaration
--     | method_declaration
--     | property_declaration
--     | event_declaration
--     | indexer_declaration
--     | operator_declaration
--     | constructor_declaration
--     | static_constructor_declaration
--     | type_declaration
--     | fixed_size_buffer_declaration   // unsafe code support
--     ;

      def "StructMemberDeclaration" $ union [
        "constant">: csharp "ConstantDeclaration",
        "field">: csharp "FieldDeclaration",
        "method">: csharp "MethodDeclaration",
        "property">: csharp "PropertyDeclaration",
        "event">: csharp "EventDeclaration",
        "indexer">: csharp "IndexerDeclaration",
        "operator">: csharp "OperatorDeclaration",
        "constructor">: csharp "ConstructorDeclaration",
        "staticConstructor">: csharp "StaticConstructorDeclaration",
        "type">: csharp "TypeDeclaration",
        "fixedSizeBuffer">: csharp "FixedSizeBufferDeclaration"],

-- // Source: §17.7 Array initializers
-- array_initializer
--     : '{' variable_initializer_list? '}'
--     | '{' variable_initializer_list ',' '}'
--     ;

      def "ArrayInitializer" $ wrap $
        list $ csharp "VariableInitializer",

-- variable_initializer_list
--     : variable_initializer (',' variable_initializer)*
--     ;
--
-- variable_initializer
--     : expression
--     | array_initializer
--     ;

      def "VariableInitializer" $ union [
        "expression">: csharp "Expression",
        "array">: csharp "ArrayInitializer"],

-- // Source: §18.2.1 General
-- interface_declaration
--     : attributes? interface_modifier* 'partial'? 'interface'
--       identifier variant_type_parameter_list? interface_base?
--       type_parameter_constraints_clause* interface_body ';'?
--     ;

      def "InterfaceDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "InterfaceModifier",
        "partial">: boolean,
        "name">: csharp "Identifier",
        "parameters">: optional $ csharp "VariantTypeParameters",
        "base">: list $ csharp "InterfaceType",
        "constraints">: list $ csharp "TypeParameterConstraintsClause",
        "body">: list $ csharp "InterfaceMemberDeclaration"],

-- // Source: §18.2.2 Interface modifiers
-- interface_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "InterfaceModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private",
        "unsafe"],

-- // Source: §18.2.3.1 General
-- variant_type_parameter_list
--     : '<' variant_type_parameters '>'
--     ;
--
-- // Source: §18.2.3.1 General
-- variant_type_parameters
--     : attributes? variance_annotation? type_parameter
--     | variant_type_parameters ',' attributes? variance_annotation?
--       type_parameter
--     ;

      def "VariantTypeParameters" $ list $ csharp "VariantTypeParameter",

      def "VariantTypeParameter" $ record [
        "attributes">: optional $ csharp "Attributes",
        "variance">: optional $ csharp "VarianceAnnotation",
        "parameter">: csharp "TypeParameter"],

-- // Source: §18.2.3.1 General
-- variance_annotation
--     : 'in'
--     | 'out'
--     ;

      def "VarianceAnnotation" $ enum [
        "in",
        "out"],

-- // Source: §18.2.4 Base interfaces
-- interface_base
--     : ':' interface_type_list
--     ;
--
-- // Source: §18.3 Interface body
-- interface_body
--     : '{' interface_member_declaration* '}'
--     ;
--
-- // Source: §18.4.1 General
-- interface_member_declaration
--     : interface_method_declaration
--     | interface_property_declaration
--     | interface_event_declaration
--     | interface_indexer_declaration
--     ;

      def "InterfaceMemberDeclaration" $ union [
        "method">: csharp "InterfaceMethodDeclaration",
        "property">: csharp "InterfacePropertyDeclaration",
        "event">: csharp "InterfaceEventDeclaration",
        "indexer">: csharp "InterfaceIndexerDeclaration"],

-- // Source: §18.4.2 Interface methods
-- interface_method_declaration
--     : attributes? 'new'? return_type interface_method_header
--     | attributes? 'new'? ref_kind ref_return_type interface_method_header
--     ;

      def "InterfaceMethodDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "new">: boolean,
        "returnType">: csharp "ReturnType",
        "refKind">: optional $ csharp "RefKind",
        "header">: csharp "InterfaceMethodHeader"],

-- interface_method_header
--     : identifier '(' formal_parameter_list? ')' ';'
--     | identifier type_parameter_list '(' formal_parameter_list? ')'
--       type_parameter_constraints_clause* ';'
--     ;

      def "InterfaceMethodHeader" $ record [
        "name">: csharp "Identifier",
        "parameters">: optional $ csharp "FormalParameterList",
        "typeParameters">: optional $ csharp "TypeParameterList",
        "constraints">: list $ csharp "TypeParameterConstraintsClause"],

-- // Source: §18.4.3 Interface properties
-- interface_property_declaration
--     : attributes? 'new'? type identifier '{' interface_accessors '}'
--     | attributes? 'new'? ref_kind type identifier '{' ref_interface_accessor '}'
--     ;

      def "InterfacePropertyDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "new">: boolean,
        "refKind">: optional $ csharp "RefKind",
        "type">: csharp "Type",
        "name">: csharp "Identifier",
        "accessors">: csharp "InterfaceAccessors"],

-- interface_accessors
--     : attributes? 'get' ';'
--     | attributes? 'set' ';'
--     | attributes? 'get' ';' attributes? 'set' ';'
--     | attributes? 'set' ';' attributes? 'get' ';'
--     ;

      def "InterfaceAccessors" $ record [
        "attributes">: optional $ csharp "Attributes",
        "get">: optional $ csharp "Attributes",
        "set">: optional $ csharp "Attributes"],

-- ref_interface_accessor
--     : attributes? 'get' ';'
--     ;
--
-- // Source: §18.4.4 Interface events
-- interface_event_declaration
--     : attributes? 'new'? 'event' type identifier ';'
--     ;

      def "InterfaceEventDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "new">: boolean,
        "type">: csharp "Type",
        "name">: csharp "Identifier"],

-- // Source: §18.4.5 Interface indexers
-- interface_indexer_declaration
--     : attributes? 'new'? type 'this' '[' formal_parameter_list ']'
--       '{' interface_accessors '}'
--     | attributes? 'new'? ref_kind type 'this' '[' formal_parameter_list ']'
--       '{' ref_interface_accessor '}'
--     ;

      def "InterfaceIndexerDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "new">: boolean,
        "refKind">: optional $ csharp "RefKind",
        "type">: csharp "Type",
        "parameters">: csharp "FormalParameterList",
        "accessors">: csharp "InterfaceAccessors"],

-- // Source: §19.2 Enum declarations
-- enum_declaration
--     : attributes? enum_modifier* 'enum' identifier enum_base? enum_body ';'?
--     ;

      def "EnumDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "EnumModifier",
        "name">: csharp "Identifier",
        "base">: optional $ csharp "EnumBase",
        "body">: optional $ csharp "EnumBody"],

-- enum_base
--     : ':' integral_type
--     | ':' integral_type_name
--     ;

      def "EnumBase" $ union [
        "type">: csharp "IntegralType",
        "name">: csharp "TypeName"],

-- integral_type_name
--     : type_name // Shall resolve to an integral type other than char
--     ;
--
-- enum_body
--     : '{' enum_member_declarations? '}'
--     | '{' enum_member_declarations ',' '}'
--     ;

      def "EnumBody" $ wrap $
        list $ csharp "EnumMemberDeclaration",

-- // Source: §19.3 Enum modifiers
-- enum_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     ;

      def "EnumModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private"],

-- // Source: §19.4 Enum members
-- enum_member_declarations
--     : enum_member_declaration (',' enum_member_declaration)*
--     ;
--
-- // Source: §19.4 Enum members
-- enum_member_declaration
--     : attributes? identifier ('=' constant_expression)?
--     ;

      def "EnumMemberDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "name">: csharp "Identifier",
        "value">: optional $ csharp "ConstantExpression"],

-- // Source: §20.2 Delegate declarations
-- delegate_declaration
--     : attributes? delegate_modifier* 'delegate' return_type delegate_header
--     | attributes? delegate_modifier* 'delegate' ref_kind ref_return_type
--       delegate_header
--     ;

      def "DelegateDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: list $ csharp "DelegateModifier",
        "returnType">: csharp "ReturnType",
        "refKind">: optional $ csharp "RefKind",
        "refReturnType">: optional $ csharp "Type",
        "header">: csharp "DelegateHeader"],

-- delegate_header
--     : identifier '(' formal_parameter_list? ')' ';'
--     | identifier variant_type_parameter_list '(' formal_parameter_list? ')'
--       type_parameter_constraints_clause* ';'
--     ;

      def "DelegateHeader" $ record [
        "name">: csharp "Identifier",
        "typeParameters">: optional $ csharp "VariantTypeParameters",
        "parameters">: optional $ csharp "FormalParameterList",
        "constraints">: list $ csharp "TypeParameterConstraintsClause"],

-- delegate_modifier
--     : 'new'
--     | 'public'
--     | 'protected'
--     | 'internal'
--     | 'private'
--     | unsafe_modifier   // unsafe code support
--     ;

      def "DelegateModifier" $ enum [
        "new",
        "public",
        "protected",
        "internal",
        "private",
        "unsafe"],

-- // Source: §22.3 Attribute specification
-- global_attributes
--     : global_attribute_section+
--     ;
--
-- global_attribute_section
--     : '[' global_attribute_target_specifier attribute_list ']'
--     | '[' global_attribute_target_specifier attribute_list ',' ']'
--     ;

      def "GlobalAttributeSection" $ record [
        "target">: csharp "Identifier",
        "attributes">: csharp "AttributeList"],

-- global_attribute_target_specifier
--     : global_attribute_target ':'
--     ;
--
-- global_attribute_target
--     : identifier
--     ;
--
-- attributes
--     : attribute_section+
--     ;

      def "Attributes" $ wrap $
        nonemptyList $ csharp "AttributeSection",

-- attribute_section
--     : '[' attribute_target_specifier? attribute_list ']'
--     | '[' attribute_target_specifier? attribute_list ',' ']'
--     ;

      def "AttributeSection" $ record [
        "target">: optional $ csharp "AttributeTarget",
        "attributes">: csharp "AttributeList"],

-- attribute_target_specifier
--     : attribute_target ':'
--     ;
--
-- attribute_target
--     : identifier
--     | keyword
--     ;

      def "AttributeTarget" $ union [
        "identifier">: csharp "Identifier",
        "keyword">: csharp "Keyword"],

-- attribute_list
--     : attribute (',' attribute)*
--     ;

      def "AttributeList" $ nonemptyList $ csharp "Attribute",

-- attribute
--     : attribute_name attribute_arguments?
--     ;

      def "Attribute" $ record [
        "name">: csharp "AttributeName",
        "arguments">: optional $ csharp "AttributeArguments"],

-- attribute_name
--     : type_name
--     ;

      def "AttributeName" $ wrap $
        csharp "TypeName",

-- attribute_arguments
--     : '(' ')'
--     | '(' positional_argument_list (',' named_argument_list)? ')'
--     | '(' named_argument_list ')'
--     ;

      def "AttributeArguments" $ record [
        "positonal">: optional $ csharp "PositionalArgumentList",
        "named">: optional $ csharp "NamedArgumentList"],

-- positional_argument_list
--     : positional_argument (',' positional_argument)*
--     ;

      def "PositionalArgumentList" $ nonemptyList $ csharp "PositionalArgument",

-- positional_argument
--     : argument_name? attribute_argument_expression
--     ;

      def "PositionalArgument" $ record [
        "name">: optional $ csharp "Identifier",
        "value">: csharp "AttributeArgumentExpression"],

-- named_argument_list
--     : named_argument (','  named_argument)*
--     ;

      def "NamedArgumentList" $ nonemptyList $ csharp "NamedArgument",

-- named_argument
--     : identifier '=' attribute_argument_expression
--     ;

      def "NamedArgument" $ record [
        "name">: csharp "Identifier",
        "value">: csharp "AttributeArgumentExpression"],

-- attribute_argument_expression
--     : non_assignment_expression
--     ;

      def "AttributeArgumentExpression" $ wrap $
        csharp "NonAssignmentExpression"]

    unsafeElements = [

-- // Source: §23.2 Unsafe contexts
-- unsafe_modifier
--     : 'unsafe'
--     ;
--
-- unsafe_statement
--     : 'unsafe' block
--     ;
--
-- // Source: §23.3 Pointer types
-- pointer_type
--     : value_type ('*')+
--     | 'void' ('*')+
--     ;

      def "PointerType" $ union [
        "valueType">: optional $ csharp "ValueType",
        "pointerDepth">: int32], -- Note: positive integer

-- // Source: §23.6.2 Pointer indirection
-- pointer_indirection_expression
--     : '*' unary_expression
--     ;
--
-- // Source: §23.6.3 Pointer member access
-- pointer_member_access
--     : primary_expression '->' identifier type_argument_list?
--     ;

      def "PointerMemberAccess" $ record [
        "pointer">: csharp "PrimaryExpression",
        "member">: csharp "Identifier",
        "typeArguments">: optional $ csharp "TypeArgumentList"],

-- // Source: §23.6.4 Pointer element access
-- pointer_element_access
--     : primary_no_array_creation_expression '[' expression ']'
--     ;

      def "PointerElementAccess" $ record [
        "pointer">: csharp "PrimaryNoArrayCreationExpression",
        "index">: csharp "Expression"],

-- // Source: §23.6.5 The address-of operator
-- addressof_expression
--     : '&' unary_expression
--     ;
--
-- // Source: §23.7 The fixed statement
-- fixed_statement
--     : 'fixed' '(' pointer_type fixed_pointer_declarators ')' embedded_statement
--     ;

      def "FixedStatement" $ record [
        "pointerType">: csharp "PointerType",
        "declarators">: nonemptyList $ csharp "FixedPointerDeclarator",
        "statement">: csharp "EmbeddedStatement"],

-- fixed_pointer_declarators
--     : fixed_pointer_declarator (','  fixed_pointer_declarator)*
--     ;
--
-- fixed_pointer_declarator
--     : identifier '=' fixed_pointer_initializer
--     ;
--
-- fixed_pointer_initializer
--     : '&' variable_reference
--     | expression
--     ;

      def "FixedPointerDeclarator" $ union [
        "reference">: csharp "VariableReference",
        "expression">: csharp "Expression"],

-- // Source: §23.8.2 Fixed-size buffer declarations
-- fixed_size_buffer_declaration
--     : attributes? fixed_size_buffer_modifier* 'fixed' buffer_element_type
--       fixed_size_buffer_declarators ';'
--     ;

      def "FixedSizeBufferDeclaration" $ record [
        "attributes">: optional $ csharp "Attributes",
        "modifiers">: nonemptyList $ csharp "FixedSizeBufferModifier",
        "elementType">: csharp "Type",
        "declarators">: nonemptyList $ csharp "FixedSizeBufferDeclarator"],

-- fixed_size_buffer_modifier
--     : 'new'
--     | 'public'
--     | 'internal'
--     | 'private'
--     | 'unsafe'
--     ;

      def "FixedSizeBufferModifier" $ enum [
        "new",
        "public",
        "internal",
        "private",
        "unsafe"],

-- buffer_element_type
--     : type
--     ;
--
-- fixed_size_buffer_declarators
--     : fixed_size_buffer_declarator (',' fixed_size_buffer_declarator)*
--     ;
--
-- fixed_size_buffer_declarator
--     : identifier '[' constant_expression ']'
--     ;

      def "FixedSizeBufferDeclarator" $ record [
        "name">: csharp "Identifier",
        "size">: csharp "ConstantExpression"]]
