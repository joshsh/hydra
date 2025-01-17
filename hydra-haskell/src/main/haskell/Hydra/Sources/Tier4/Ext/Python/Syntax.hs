{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Ext.Python.Syntax where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types


pythonNs = Namespace "hydra/ext/python/syntax"
python = typeref pythonNs

pythonSyntaxModule :: Module
pythonSyntaxModule = Module pythonNs elements [hydraCoreModule] tier0Modules $
    Just ("A Python syntax model, based on the Python v3 PEG grammar retrieved on 2024-12-22"
      ++ " from https://docs.python.org/3/reference/grammar.html")
  where
    def = datatype pythonNs

    elements = constructs ++ terminals ++ nonterminals

    -- These definitions are not based on the grammar, but are convenient for working with Python sources in Hydra.
    constructs = [
      def "AnnotatedStatement" $ record [ -- Note: added for Hydra-Python
        "comment">: string,
        "statement">: python "Statement"],

      def "Module" $ record [
        "imports">: list $ python "ImportStatement",
        "comment">: optional string,
        "body">: list $ python "Statement"]]

    -- Terminals from the PEG grammar (see below)
    terminals = [
      def "Name" string, -- NAME in the grammar

      def "Number" $ union [ -- NUMBER in the grammar
        "integer">: bigint,
        "float">: bigfloat],

      def "TypeComment" string] -- TYPE_COMMENT in the grammar

    -- Nonterminal productions from the PEG grammar (inline)
    nonterminals = [
-- # General grammatical elements and rules:
-- #
-- # * Strings with double quotes (") denote SOFT KEYWORDS
-- # * Strings with single quotes (') denote KEYWORDS
-- # * Upper case names (NAME) denote tokens in the Grammar/Tokens file
-- # * Rule names starting with "invalid_" are used for specialized syntax errors
-- #     - These rules are NOT used in the first pass of the parser.
-- #     - Only if the first pass fails to parse, a second pass including the invalid
-- #       rules will be executed.
-- #     - If the parser fails in the second phase with a generic syntax error, the
-- #       location of the generic failure of the first pass will be used (this avoids
-- #       reporting incorrect locations due to the invalid rules).
-- #     - The order of the alternatives involving invalid rules matter
-- #       (like any rule in PEG).
-- #
-- # Grammar Syntax (see PEP 617 for more information):
-- #
-- # rule_name: expression
-- #   Optionally, a type can be included right after the rule name, which
-- #   specifies the return type of the C or Python function corresponding to the
-- #   rule:
-- # rule_name[return_type]: expression
-- #   If the return type is omitted, then a void * is returned in C and an Any in
-- #   Python.
-- # e1 e2
-- #   Match e1, then match e2.
-- # e1 | e2
-- #   Match e1 or e2.
-- #   The first alternative can also appear on the line after the rule name for
-- #   formatting purposes. In that case, a | must be used before the first
-- #   alternative, like so:
-- #       rule_name[return_type]:
-- #            | first_alt
-- #            | second_alt
-- # ( e )
-- #   Match e (allows also to use other operators in the group like '(e)*')
-- # [ e ] or e?
-- #   Optionally match e.
-- # e*
-- #   Match zero or more occurrences of e.
-- # e+
-- #   Match one or more occurrences of e.
-- # s.e+
-- #   Match one or more occurrences of e, separated by s. The generated parse tree
-- #   does not include the separator. This is otherwise identical to (e (s e)*).
-- # &e
-- #   Succeed if e can be parsed, without consuming any input.
-- # !e
-- #   Fail if e can be parsed, without consuming any input.
-- # ~
-- #   Commit to the current alternative, even if it fails to parse.
-- # &&e
-- #   Eager parse e. The parser will not backtrack and will immediately
-- #   fail with SyntaxError if e cannot be parsed.
-- #
--
-- # STARTING RULES
-- # ==============
--
-- file: [statements] ENDMARKER

      def "File" $ list $ python "Statement",

-- interactive: statement_newline

      def "Interactive" $ python "Statement",

-- eval: expressions NEWLINE* ENDMARKER

      def "Eval" $ nonemptyList $ python "Expression",

-- func_type: '(' [type_expressions] ')' '->' expression NEWLINE* ENDMARKER

      def "FuncType" $ record [ -- TODO: func_type is defined in the official BNF grammar, but never used
        "type">: list $ python "TypeExpression",
        "body">: python "Expression"],

-- # GENERAL STATEMENTS
-- # ==================
--
-- statements: statement+
--
-- statement: compound_stmt  | simple_stmts

      def "Statement" $ union [
        "compound">: python "CompoundStatement",
        "simple">: nonemptyList $ python "SimpleStatement",
        "annotated">: python "AnnotatedStatement"], -- Added for Hydra-Python

-- statement_newline:
--     | compound_stmt NEWLINE
--     | simple_stmts
--     | NEWLINE
--     | ENDMARKER
--
-- simple_stmts:
--     | simple_stmt !';' NEWLINE  # Not needed, there for speedup
--     | ';'.simple_stmt+ [';'] NEWLINE
--
-- # NOTE: assignment MUST precede expression, else parsing a simple assignment
-- # will throw a SyntaxError.
-- simple_stmt:
--     | assignment
--     | type_alias
--     | star_expressions
--     | return_stmt
--     | import_stmt
--     | raise_stmt
--     | 'pass'
--     | del_stmt
--     | yield_stmt
--     | assert_stmt
--     | 'break'
--     | 'continue'
--     | global_stmt
--     | nonlocal_stmt

      def "SimpleStatement" $ union [
        "assignment">: python "Assignment",
        "typeAlias">: python "TypeAlias",
        "starExpressions">: nonemptyList $ python "StarExpression",
        "return">: python "ReturnStatement",
        "import">: python "ImportStatement",
        "raise">: python "RaiseStatement",
        "pass">: unit,
        "del">: python "DelStatement",
        "yield">: python "YieldStatement",
        "assert">: python "AssertStatement",
        "break">: unit,
        "continue">: unit,
        "global">: nonemptyList $ python "Name",
        "nonlocal">: nonemptyList $ python "Name"],

-- compound_stmt:
--     | function_def
--     | if_stmt
--     | class_def
--     | with_stmt
--     | for_stmt
--     | try_stmt
--     | while_stmt
--     | match_stmt

      def "CompoundStatement" $ union [
        "functionDef">: python "FunctionDefinition",
        "if">: python "IfStatement",
        "classDef">: python "ClassDefinition",
        "with">: python "WithStatement",
        "for">: python "ForStatement",
        "try">: python "TryStatement",
        "while">: python "WhileStatement",
        "match">: python "MatchStatement"],

-- # SIMPLE STATEMENTS
-- # =================
--
-- # NOTE: annotated_rhs may start with 'yield'; yield_expr must start with 'yield'
-- assignment:
--     | NAME ':' expression ['=' annotated_rhs ]
--     | ('(' single_target ')'
--          | single_subscript_attribute_target) ':' expression ['=' annotated_rhs ]
--     | (star_targets '=' )+ (yield_expr | star_expressions) !'=' [TYPE_COMMENT]
--     | single_target augassign ~ (yield_expr | star_expressions)

      def "Assignment" $ union [
        "typed">: python "TypedAssignment",
        "untyped">: python "UntypedAssignment",
        "aug">: python "AugAssignment"],

      def "TypedAssignment" $ record [
        "lhs">: python "SingleTarget",
        "type">: python "Expression",
        "rhs">: optional $ python "AnnotatedRhs"],

      def "UntypedAssignment" $ record [
        "targets">: nonemptyList $ python "StarTarget",
        "rhs">: python "AnnotatedRhs",
        "typeComment">: optional $ python "TypeComment"],

      def "AugAssignment" $ record [
        "lhs">: python "SingleTarget",
        "augassign">: python "AugAssign",
        "rhs">: python "AnnotatedRhs"],

-- annotated_rhs: yield_expr | star_expressions

      def "AnnotatedRhs" $ union [
        "yield">: python "YieldExpression",
        "star">: nonemptyList $ python "StarExpression"],

-- augassign:
--     | '+='
--     | '-='
--     | '*='
--     | '@='
--     | '/='
--     | '%='
--     | '&='
--     | '|='
--     | '^='
--     | '<<='
--     | '>>='
--     | '**='
--     | '//='

      def "AugAssign" $ enum [
        "plusEqual",
        "minusEqual",
        "timesEqual",
        "atEqual",
        "slashEqual",
        "percentEqual",
        "ampersandEqual",
        "barEqual",
        "caretEqual",
        "leftShiftEqual",
        "rightShiftEqual",
        "starStarEqual",
        "doubleSlashEqual"],

-- return_stmt:
--     | 'return' [star_expressions]

      def "ReturnStatement" $ list $ python "StarExpression",

-- raise_stmt:
--     | 'raise' expression ['from' expression ]
--     | 'raise'

      def "RaiseStatement" $ optional $ python "RaiseExpression",

      def "RaiseExpression" $ record [
        "expression">: python "Expression",
        "from">: optional $ python "Expression"],

-- global_stmt: 'global' ','.NAME+
--
-- nonlocal_stmt: 'nonlocal' ','.NAME+
--
-- del_stmt:
--     | 'del' del_targets &(';' | NEWLINE)

      def "DelStatement" $ python "DelTargets",

-- yield_stmt: yield_expr

      def "YieldStatement" $ python "YieldExpression",

-- assert_stmt: 'assert' expression [',' expression ]

      def "AssertStatement" $ record [
        "expression1">: python "Expression",
        "expression2">: optional $ python "Expression"],

-- import_stmt:
--     | import_name
--     | import_from

      def "ImportStatement" $ union [
        "name">: python "ImportName",
        "from">: python "ImportFrom"],

-- # Import statements
-- # -----------------
--
-- import_name: 'import' dotted_as_names

      def "ImportName" $ nonemptyList $ python "DottedAsName",

-- # note below: the ('.' | '...') is necessary because '...' is tokenized as ELLIPSIS
-- import_from:
--     | 'from' ('.' | '...')* dotted_name 'import' import_from_targets
--     | 'from' ('.' | '...')+ 'import' import_from_targets

      def "ImportFrom" $ record [
        "prefixes">: list $ python "RelativeImportPrefix",
        "dottedName">: optional $ python "DottedName",
        "targets">: python "ImportFromTargets"],

      def "RelativeImportPrefix" $ enum ["dot", "ellipsis"],

-- import_from_targets:
--     | '(' import_from_as_names [','] ')'
--     | import_from_as_names !','
--     | '*'

      def "ImportFromTargets" $ union [
        "simple">: nonemptyList $ python "ImportFromAsName",
        "parens">: nonemptyList $ python "ImportFromAsName",
        "star">: unit],

-- import_from_as_names:
--     | ','.import_from_as_name+
--
-- import_from_as_name:
--     | NAME ['as' NAME ]

      def "ImportFromAsName" $ record [
        "name">: python "Name",
        "as">: optional $ python "Name"],

-- dotted_as_names:
--     | ','.dotted_as_name+
--
-- dotted_as_name:
--     | dotted_name ['as' NAME ]

      def "DottedAsName" $ record [
        "name">: python "DottedName",
        "as">: optional $ python "Name"],

-- dotted_name:
--     | dotted_name '.' NAME
--     | NAME

      def "DottedName" $ nonemptyList $ python "Name",

--
-- # COMPOUND STATEMENTS
-- # ===================
--
-- # Common elements
-- # ---------------
--
-- block:
--     | NEWLINE INDENT statements DEDENT
--     | simple_stmts

      def "Block" $ union [
        "indented">: nonemptyList $ python "Statement",
        "simple">: nonemptyList $ python "SimpleStatement"],

-- decorators: ('@' named_expression NEWLINE )+

       def "Decorators" $ nonemptyList $ python "NamedExpression",

-- # Class definitions
-- # -----------------
--
-- class_def:
--     | decorators class_def_raw
--     | class_def_raw

      def "ClassDefinition" $ record [
        "decorators">: optional $ python "Decorators",
        "name">: python "Name",
        "typeParams">: list $ python "TypeParameter",
        "arguments">: optional $ python "Args",
        "comment">: optional string, -- Added for Hydra
        "block">: python "Block"],

-- class_def_raw:
--     | 'class' NAME [type_params] ['(' [arguments] ')' ] ':' block
--
-- # Function definitions
-- # --------------------
--
-- function_def:
--     | decorators function_def_raw
--     | function_def_raw

      def "FunctionDefinition" $ record [
        "decorators">: optional $ python "Decorators",
        "raw">: python "FunctionDefRaw"],

-- function_def_raw:
--     | 'def' NAME [type_params] '(' [params] ')' ['->' expression ] ':' [func_type_comment] block
--     | 'async' 'def' NAME [type_params] '(' [params] ')' ['->' expression ] ':' [func_type_comment] block

      def "FunctionDefRaw" $ record [
        "async">: boolean,
        "name">: python "Name",
        "typeParams">: list $ python "TypeParameter",
        "params">: optional $ python "Params",
        "returnType">: optional $ python "Expression",
        "funcTypeComment">: optional $ python "FuncTypeComment",
        "block">: python "Block"],

-- # Function parameters
-- # -------------------
--
-- params:
--     | parameters

      def "Params" $ python "Parameters",

-- parameters:
--     | slash_no_default param_no_default* param_with_default* [star_etc]
--     | slash_with_default param_with_default* [star_etc]
--     | param_no_default+ param_with_default* [star_etc]
--     | param_with_default+ [star_etc]
--     | star_etc

      def "Parameters" $ union [
        "slashNoDefault">: python "SlashNoDefaultParameters",
        "slashWithDefault">: python "SlashWithDefaultParameters",
        "paramNoDefault">: python "ParamNoDefaultParameters",
        "paramWithDefault">: python "ParamWithDefaultParameters",
        "starEtc">: python "StarEtc"],

      def "SlashNoDefaultParameters" $ record [
        "slash">: python "SlashNoDefault",
        "paramNoDefault">: list $ python "ParamNoDefault",
        "paramWithDefault">: list $ python "ParamWithDefault",
        "starEtc">: optional $ python "StarEtc"],

      def "SlashWithDefaultParameters" $ record [
        "paramNoDefault">: list $ python "ParamNoDefault",
        "paramWithDefault">: list $ python "ParamWithDefault",
        "starEtc">: optional $ python "StarEtc"],

      def "ParamNoDefaultParameters" $ record [
        "paramNoDefault">: nonemptyList $ python "ParamNoDefault",
        "paramWithDefault">: list $ python "ParamWithDefault",
        "starEtc">: optional $ python "StarEtc"],

      def "ParamWithDefaultParameters" $ record [
        "paramWithDefault">: nonemptyList $ python "ParamWithDefault",
        "starEtc">: optional $ python "StarEtc"],

-- # Some duplication here because we can't write (',' | &')'),
-- # which is because we don't support empty alternatives (yet).
--
-- slash_no_default:
--     | param_no_default+ '/' ','
--     | param_no_default+ '/' &')'

      def "SlashNoDefault" $ nonemptyList $ python "ParamNoDefault",

-- slash_with_default:
--     | param_no_default* param_with_default+ '/' ','
--     | param_no_default* param_with_default+ '/' &')'

      def "SlashWithDefault" $ record [
        "paramNoDefault">: list $ python "ParamNoDefault",
        "paramWithDefault">: nonemptyList $ python "ParamWithDefault"],

-- star_etc:
--     | '*' param_no_default param_maybe_default* [kwds]
--     | '*' param_no_default_star_annotation param_maybe_default* [kwds]
--     | '*' ',' param_maybe_default+ [kwds]
--     | kwds

      def "StarEtc" $ union [
        "starNoDefault">: python "NoDefaultStarEtc",
        "starNoDefaultStarAnnotation">: python "NoDefaultStarAnnotationStarEtc",
        "starComma">: python "CommaStarEtc",
        "keywords">: python "Keywords"],

      def "NoDefaultStarEtc" $ record [
        "paramNoDefault">: python "ParamNoDefault",
        "paramMaybeDefault">: list $ python "ParamMaybeDefault",
        "keywords">: optional $ python "Keywords"],

      def "NoDefaultStarAnnotationStarEtc" $ record [
        "paramNoDefaultStarAnnotation">: python "ParamNoDefaultStarAnnotation",
        "paramMaybeDefault">: list $ python "ParamMaybeDefault",
        "keywords">: optional $ python "Keywords"],

      def "CommaStarEtc" $ record [
        "paramMaybeDefault">: nonemptyList $ python "ParamMaybeDefault",
        "keywords">: optional $ python "Keywords"],

-- kwds:
--     | '**' param_no_default

      def "Keywords" $ python "ParamNoDefault",

-- # One parameter.  This *includes* a following comma and type comment.
-- #
-- # There are three styles:
-- # - No default
-- # - With default
-- # - Maybe with default
-- #
-- # There are two alternative forms of each, to deal with type comments:
-- # - Ends in a comma followed by an optional type comment
-- # - No comma, optional type comment, must be followed by close paren
-- # The latter form is for a final parameter without trailing comma.
-- #
--
-- param_no_default:
--     | param ',' TYPE_COMMENT?
--     | param TYPE_COMMENT? &')'

      def "ParamNoDefault" $ record [
        "param">: python "Param",
        "typeComment">: optional $ python "TypeComment"],

-- param_no_default_star_annotation:
--     | param_star_annotation ',' TYPE_COMMENT?
--     | param_star_annotation TYPE_COMMENT? &')'

      def "ParamNoDefaultStarAnnotation" $ record [
        "paramStarAnnotation">: python "ParamStarAnnotation",
        "typeComment">: optional $ python "TypeComment"],

-- param_with_default:
--     | param default ',' TYPE_COMMENT?
--     | param default TYPE_COMMENT? &')'

      def "ParamWithDefault" $ record [
        "param">: python "Param",
        "default">: python "Default",
        "typeComment">: optional $ python "TypeComment"],

-- param_maybe_default:
--     | param default? ',' TYPE_COMMENT?
--     | param default? TYPE_COMMENT? &')'

      def "ParamMaybeDefault" $ record [
        "param">: python "Param",
        "default">: optional $ python "Default",
        "typeComment">: optional $ python "TypeComment"],

-- param: NAME annotation?

      def "Param" $ record [
        "name">: python "Name",
        "annotation">: optional $ python "Annotation"],

-- param_star_annotation: NAME star_annotation

      def "ParamStarAnnotation" $ record [
        "name">: python "Name",
        "annotation">: python "StarAnnotation"],

-- annotation: ':' expression

      def "Annotation" $ python "Expression",

-- star_annotation: ':' star_expression

      def "StarAnnotation" $ python "StarExpression",

-- default: '=' expression  | invalid_default

      def "Default" $ python "Expression",

-- # If statement
-- # ------------
--
-- if_stmt:
--     | 'if' named_expression ':' block elif_stmt
--     | 'if' named_expression ':' block [else_block]

      def "IfStatement" $ record [
        "condition">: python "NamedExpression",
        "body">: python "Block",
        "continuation">: optional $ python "IfTail"],

      def "IfTail" $ union [
        "elif">: python "IfStatement",
        "else">: python "Block"],

-- elif_stmt:
--     | 'elif' named_expression ':' block elif_stmt
--     | 'elif' named_expression ':' block [else_block]

-- else_block:
--     | 'else' ':' block
--
-- # While statement
-- # ---------------
--
-- while_stmt:
--     | 'while' named_expression ':' block [else_block]

      def "WhileStatement" $ record [
        "condition">: python "NamedExpression",
        "body">: python "Block",
        "else">: optional $ python "Block"],

-- # For statement
-- # -------------
--
-- for_stmt:
--     | 'for' star_targets 'in' ~ star_expressions ':' [TYPE_COMMENT] block [else_block]
--     | 'async' 'for' star_targets 'in' ~ star_expressions ':' [TYPE_COMMENT] block [else_block]

      def "ForStatement" $ record [
        "async">: boolean,
        "targets">: nonemptyList $ python "StarTarget",
        "expressions">: nonemptyList $ python "StarExpression",
        "typeComment">: optional $ python "TypeComment",
        "body">: python "Block",
        "else">: optional $ python "Block"],

-- # With statement
-- # --------------
--
-- with_stmt:
--     |         'with' '(' ','.with_item+ ','? ')' ':' [TYPE_COMMENT] block
--     |         'with' ','.with_item+ ':' [TYPE_COMMENT] block
--     | 'async' 'with' '(' ','.with_item+ ','? ')' ':' block
--     | 'async' 'with' ','.with_item+ ':' [TYPE_COMMENT] block

      def "WithStatement" $ record [
        "async">: boolean,
        "items">: nonemptyList $ python "WithItem",
        "typeComment">: optional $ python "TypeComment",
        "body">: python "Block"],

-- with_item:
--     | expression 'as' star_target &(',' | ')' | ':')
--     | expression

      def "WithItem" $ record [
        "expression">: python "Expression",
        "as">: optional $ python "StarTarget"],

-- # Try statement
-- # -------------
--
-- try_stmt:
--     | 'try' ':' block finally_block
--     | 'try' ':' block except_block+ [else_block] [finally_block]
--     | 'try' ':' block except_star_block+ [else_block] [finally_block]

      def "TryStatement" $ union [
        "finally">: python "TryFinallyStatement",
        "except">: python "TryExceptStatement",
        "exceptStar">: python "TryExceptStarStatement"],

      def "TryFinallyStatement" $ record [
        "body">: python "Block",
        "finally">: python "Block"],

      def "TryExceptStatement" $ record [
        "body">: python "Block",
        "excepts">: nonemptyList $ python "ExceptBlock",
        "else">: optional $ python "Block",
        "finally">: optional $ python "Block"],

      def "TryExceptStarStatement" $ record [
        "body">: python "Block",
        "excepts">: nonemptyList $ python "ExceptStarBlock",
        "else">: optional $ python "Block",
        "finally">: optional $ python "Block"],

-- # Except statement
-- # ----------------
--
-- except_block:
--     | 'except' expression ['as' NAME ] ':' block
--     | 'except' ':' block

      def "ExceptBlock" $ record [
        "expression">: optional $ python "ExceptExpression",
        "body">: python "Block"],

      def "ExceptExpression" $ record [
        "expression">: python "Expression",
        "as">: optional $ python "Name"],

-- except_star_block:
--     | 'except' '*' expression ['as' NAME ] ':' block

      def "ExceptStarBlock" $ record [
        "expression">: python "Expression",
        "as">: optional $ python "Name",
        "body">: python "Block"],

-- finally_block:
--     | 'finally' ':' block
--
-- # Match statement
-- # ---------------
--
-- match_stmt:
--     | "match" subject_expr ':' NEWLINE INDENT case_block+ DEDENT

      def "MatchStatement" $ record [
        "subject">: python "SubjectExpression",
        "cases">: nonemptyList $ python "CaseBlock"],

-- subject_expr:
--     | star_named_expression ',' star_named_expressions?
--     | named_expression

      def "SubjectExpression" $ union [
        "tuple">: nonemptyList $ python "StarNamedExpression",
        "expression">: python "NamedExpression"],

-- case_block:
--     | "case" patterns guard? ':' block

      def "CaseBlock" $ record [
        "patterns">: python "Patterns",
        "guard">: optional $ python "Guard",
        "body">: python "Block"],

-- guard: 'if' named_expression

      def "Guard" $ python "NamedExpression",

-- patterns:
--     | open_sequence_pattern
--     | pattern

      def "Patterns" $ union [
        "sequence">: python "OpenSequencePattern",
        "pattern">: python "Pattern"],

-- pattern:
--     | as_pattern
--     | or_pattern

      def "Pattern" $ union [
        "as">: python "AsPattern",
        "or">: python "OrPattern"],

-- as_pattern:
--     | or_pattern 'as' pattern_capture_target

      def "AsPattern" $ record [
        "pattern">: python "OrPattern",
        "as">: python "PatternCaptureTarget"],

-- or_pattern:
--     | '|'.closed_pattern+

      def "OrPattern" $ nonemptyList $ python "ClosedPattern",

-- closed_pattern:
--     | literal_pattern
--     | capture_pattern
--     | wildcard_pattern
--     | value_pattern
--     | group_pattern
--     | sequence_pattern
--     | mapping_pattern
--     | class_pattern

      def "ClosedPattern" $ union [
        "literal">: python "LiteralExpression",
        "capture">: python "CapturePattern",
        "wildcard">: unit,
        "value">: python "ValuePattern",
        "group">: python "GroupPattern",
        "sequence">: python "SequencePattern",
        "mapping">: python "MappingPattern",
        "class">: python "ClassPattern"],

-- # Literal patterns are used for equality and identity constraints
-- literal_pattern:
--     | signed_number !('+' | '-')
--     | complex_number
--     | strings
--     | 'None'
--     | 'True'
--     | 'False'

      -- Note: identical to literal_expr

-- # Literal expressions are used to restrict permitted mapping pattern keys
-- literal_expr:
--     | signed_number !('+' | '-')
--     | complex_number
--     | strings
--     | 'None'
--     | 'True'
--     | 'False'

      def "LiteralExpression" $ union [
        "number">: python "SignedNumber",
        "complex">: python "ComplexNumber",
        "string">: string,
        "none">: unit,
        "true">: unit,
        "false">: unit],

-- complex_number:
--     | signed_real_number '+' imaginary_number
--     | signed_real_number '-' imaginary_number

      def "ComplexNumber" $ record [
        "real">: python "SignedRealNumber",
        "plusOrMinus">: python "PlusOrMinus",
        "imaginary">: python "ImaginaryNumber"],

      def "PlusOrMinus" $ enum ["plus", "minus"],

-- signed_number:
--     | NUMBER
--     | '-' NUMBER

      def "SignedNumber" $ union [
        "sign">: python "PlusOrMinus",
        "number">: python "Number"],

-- signed_real_number:
--     | real_number
--     | '-' real_number

      def "SignedRealNumber" $ union [
        "sign">: python "PlusOrMinus",
        "number">: python "RealNumber"],

-- real_number:
--     | NUMBER

      def "RealNumber" $ python "Number",

-- imaginary_number:
--     | NUMBER

      def "ImaginaryNumber" $ python "Number",

-- capture_pattern:
--     | pattern_capture_target

      def "CapturePattern" $ python "PatternCaptureTarget",

-- pattern_capture_target:
--     | !"_" NAME !('.' | '(' | '=')

      def "PatternCaptureTarget" $ python "Name",

-- wildcard_pattern:
--     | "_"
--
-- value_pattern:
--     | attr !('.' | '(' | '=')

      def "ValuePattern" $ python "Attribute",

-- attr:
--     | name_or_attr '.' NAME

      def "Attribute" $ nonemptyList $ python "Name", -- Actually list with length >= 2

-- name_or_attr:
--     | attr
--     | NAME

      def "NameOrAttribute" $ nonemptyList $ python "Name",

-- group_pattern:
--     | '(' pattern ')'

      def "GroupPattern" $ python "Pattern",

-- sequence_pattern:
--     | '[' maybe_sequence_pattern? ']'
--     | '(' open_sequence_pattern? ')'

      def "SequencePattern" $ union [
        "list">: optional $ python "MaybeSequencePattern",
        "tuple">: optional $ python "OpenSequencePattern"],

-- open_sequence_pattern:
--     | maybe_star_pattern ',' maybe_sequence_pattern?

      def "OpenSequencePattern" $ record [
        "head">: python "MaybeStarPattern",
        "tail">: optional $ python "MaybeSequencePattern"],

-- maybe_sequence_pattern:
--     | ','.maybe_star_pattern+ ','?

      def "MaybeSequencePattern" $ nonemptyList $ python "MaybeStarPattern",

-- maybe_star_pattern:
--     | star_pattern
--     | pattern

      def "MaybeStarPattern" $ union [
        "star">: python "StarPattern",
        "pattern">: python "Pattern"],

-- star_pattern:
--     | '*' pattern_capture_target
--     | '*' wildcard_pattern

      def "StarPattern" $ union [
        "capture">: python "PatternCaptureTarget",
        "wildcard">: unit],

-- mapping_pattern:
--     | '{' '}'
--     | '{' double_star_pattern ','? '}'
--     | '{' items_pattern ',' double_star_pattern ','? '}'
--     | '{' items_pattern ','? '}'

      def "MappingPattern" $ record [
        "items">: optional $ python "ItemsPattern",
        "doubleStar">: optional $ python "DoubleStarPattern"],

-- items_pattern:
--     | ','.key_value_pattern+

      def "ItemsPattern" $ nonemptyList $ python "KeyValuePattern",

-- key_value_pattern:
--     | (literal_expr | attr) ':' pattern

      def "KeyValuePattern" $ record [
        "key">: python "LiteralExpressionOrAttribute",
        "value">: python "Pattern"],

      def "LiteralExpressionOrAttribute" $ union [
        "literal">: python "LiteralExpression",
        "attribute">: python "Attribute"],

-- double_star_pattern:
--     | '**' pattern_capture_target

      def "DoubleStarPattern" $ python "PatternCaptureTarget",

-- class_pattern:
--     | name_or_attr '(' ')'
--     | name_or_attr '(' positional_patterns ','? ')'
--     | name_or_attr '(' keyword_patterns ','? ')'
--     | name_or_attr '(' positional_patterns ',' keyword_patterns ','? ')'

      def "ClassPattern" $ record [
        "nameOrAttribute">: python "NameOrAttribute",
        "positionalPatterns">: optional $ python "PositionalPatterns",
        "keywordPatterns">: optional $ python "KeywordPatterns"],

-- positional_patterns:
--     | ','.pattern+

      def "PositionalPatterns" $ nonemptyList $ python "Pattern",

-- keyword_patterns:
--     | ','.keyword_pattern+

      def "KeywordPatterns" $ nonemptyList $ python "KeywordPattern",

-- keyword_pattern:
--     | NAME '=' pattern

      def "KeywordPattern" $ record [
        "name">: python "Name",
        "pattern">: python "Pattern"],

-- # Type statement
-- # ---------------
--
-- type_alias:
--     | "type" NAME [type_params] '=' expression

      def "TypeAlias" $ record [
        "name">: python "Name",
        "typeParams">: list $ python "TypeParameter",
        "expression">: python "Expression"],

-- # Type parameter declaration
-- # --------------------------
--
-- type_params:
--     | invalid_type_params
--     | '[' type_param_seq ']'
--
-- type_param_seq: ','.type_param+ [',']
--
-- type_param:
--     | NAME [type_param_bound] [type_param_default]
--     | '*' NAME [type_param_starred_default]
--     | '**' NAME [type_param_default]

      def "TypeParameter" $ union [
        "simple">: python "SimpleTypeParameter",
        "star">: python "StarTypeParameter",
        "doubleStar">: python "DoubleStarTypeParameter"],

      def "SimpleTypeParameter" $ record [
        "name">: python "Name",
        "bound">: optional $ python "Expression",
        "default">: optional $ python "Expression"],

      def "StarTypeParameter" $ record [
        "name">: python "Name",
        "default">: optional $ python "StarExpression"],

      def "DoubleStarTypeParameter" $ record [
        "name">: python "Name",
        "default">: optional $ python "Expression"],

-- type_param_bound: ':' expression
-- type_param_default: '=' expression
-- type_param_starred_default: '=' star_expression
--
-- # EXPRESSIONS
-- # -----------
--
-- expressions:
--     | expression (',' expression )+ [',']
--     | expression ','
--     | expression
--
-- expression:
--     | disjunction 'if' disjunction 'else' expression
--     | disjunction
--     | lambdef

      def "Expression" $ union [
        "conditional">: python "Conditional",
        "simple">: python "Disjunction",
        "lambda">: python "Lambda"],

      def "Conditional" $ record [
        "body">: python "Disjunction",
        "if">: python "Disjunction",
        "else">: python "Expression"],

-- yield_expr:
--     | 'yield' 'from' expression
--     | 'yield' [star_expressions]

      def "YieldExpression" $ union [
        "from">: python "Expression",
        "simple">: list $ python "StarExpression"],

-- star_expressions:
--     | star_expression (',' star_expression )+ [',']
--     | star_expression ','
--     | star_expression
--
-- star_expression:
--     | '*' bitwise_or
--     | expression

      def "StarExpression" $ union [
        "star">: python "BitwiseOr",
        "simple">: python "Expression"],

-- star_named_expressions: ','.star_named_expression+ [',']

      def "StarNamedExpressions" $ nonemptyList $ python "StarNamedExpression",

-- star_named_expression:
--     | '*' bitwise_or
--     | named_expression

      def "StarNamedExpression" $ union [
        "star">: python "BitwiseOr",
        "simple">: python "NamedExpression"],

-- assignment_expression:
--     | NAME ':=' ~ expression

      def "AssignmentExpression" $ record [
        "name">: python "Name",
        "expression">: python "Expression"],

-- named_expression:
--     | assignment_expression
--     | expression !':='

      def "NamedExpression" $ union [
        "assignment">: python "AssignmentExpression",
        "simple">: python "Expression"],

-- disjunction:
--     | conjunction ('or' conjunction )+
--     | conjunction

      def "Disjunction" $ nonemptyList $ python "Conjunction",

-- conjunction:
--     | inversion ('and' inversion )+
--     | inversion

      def "Conjunction" $ nonemptyList $ python "Inversion",

-- inversion:
--     | 'not' inversion
--     | comparison

      def "Inversion" $ union [
        "not">: python "Inversion",
        "simple">: python "Comparison"],

-- # Comparison operators
-- # --------------------
--
-- comparison:
--     | bitwise_or compare_op_bitwise_or_pair+
--     | bitwise_or

      def "Comparison" $ record [
        "lhs">: python "BitwiseOr",
        "rhs">: list $ python "CompareOpBitwiseOrPair"],

-- compare_op_bitwise_or_pair:
--     | eq_bitwise_or
--     | noteq_bitwise_or
--     | lte_bitwise_or
--     | lt_bitwise_or
--     | gte_bitwise_or
--     | gt_bitwise_or
--     | notin_bitwise_or
--     | in_bitwise_or
--     | isnot_bitwise_or
--     | is_bitwise_or

      def "CompareOpBitwiseOrPair" $ record [
        "operator">: python "CompareOp",
        "rhs">: python "BitwiseOr"],

      def "CompareOp" $ enum [
        "eq", "noteq", "lte", "lt", "gte", "gt", "notin", "in", "isnot", "is"],

-- eq_bitwise_or: '==' bitwise_or
-- noteq_bitwise_or:
--     | ('!=' ) bitwise_or
-- lte_bitwise_or: '<=' bitwise_or
-- lt_bitwise_or: '<' bitwise_or
-- gte_bitwise_or: '>=' bitwise_or
-- gt_bitwise_or: '>' bitwise_or
-- notin_bitwise_or: 'not' 'in' bitwise_or
-- in_bitwise_or: 'in' bitwise_or
-- isnot_bitwise_or: 'is' 'not' bitwise_or
-- is_bitwise_or: 'is' bitwise_or
--
-- # Bitwise operators
-- # -----------------
--
-- bitwise_or:
--     | bitwise_or '|' bitwise_xor
--     | bitwise_xor

      def "BitwiseOr" $ record [
        "lhs">: optional $ python "BitwiseOr",
        "rhs">: python "BitwiseXor"],

-- bitwise_xor:
--     | bitwise_xor '^' bitwise_and
--     | bitwise_and

      def "BitwiseXor" $ record [
        "lhs">: optional $ python "BitwiseXor",
        "rhs">: python "BitwiseAnd"],

-- bitwise_and:
--     | bitwise_and '&' shift_expr
--     | shift_expr

      def "BitwiseAnd" $ record [
        "lhs">: optional $ python "BitwiseAnd",
        "rhs">: python "ShiftExpression"],

-- shift_expr:
--     | shift_expr '<<' sum
--     | shift_expr '>>' sum
--     | sum

      def "ShiftExpression" $ record [
        "lhs">: optional $ python "ShiftLhs",
        "rhs">: python "Sum"],

      def "ShiftLhs" $ record [
        "operand">: python "ShiftExpression",
        "operator">: python "ShiftOp"],

      def "ShiftOp" $ enum [
        "left", "right"],

-- # Arithmetic operators
-- # --------------------
--
-- sum:
--     | sum '+' term
--     | sum '-' term
--     | term

      def "Sum" $ record [
        "lhs">: optional $ python "SumLhs",
        "rhs">: python "Term"],

      def "SumLhs" $ record [
        "operand">: python "Sum",
        "operator">: python "SumOp"],

      def "SumOp" $ enum [
        "add", "sub"],

-- term:
--     | term '*' factor
--     | term '/' factor
--     | term '//' factor
--     | term '%' factor
--     | term '@' factor
--     | factor

      def "Term" $ record [
        "lhs">: optional $ python "TermLhs",
        "rhs">: python "Factor"],

      def "TermLhs" $ record [
        "operand">: python "Term",
        "operator">: python "TermOp"],

      def "TermOp" $ enum [
        "mul", "div", "floordiv", "mod", "matmul"],

-- factor:
--     | '+' factor
--     | '-' factor
--     | '~' factor
--     | power

      def "Factor" $ union [
        "positive">: python "Factor",
        "negative">: python "Factor",
        "complement">: python "Factor",
        "simple">: python "Power"],

-- power:
--     | await_primary '**' factor
--     | await_primary

      def "Power" $ record [
        "lhs">: python "AwaitPrimary",
        "rhs">: optional $ python "Factor"],

-- # Primary elements
-- # ----------------
--
-- # Primary elements are things like "obj.something.something", "obj[something]", "obj(something)", "obj" ...
--
-- await_primary:
--     | 'await' primary
--     | primary

      def "AwaitPrimary" $ record [
        "await">: boolean,
        "primary">: python "Primary"],

-- primary:
--     | primary '.' NAME
--     | primary genexp
--     | primary '(' [arguments] ')'
--     | primary '[' slices ']'
--     | atom

      def "Primary" $ union [
        "simple">: python "Atom",
        "compound">: python "PrimaryWithRhs"],

      def "PrimaryWithRhs" $ record [
        "primary">: python "Primary",
        "rhs">: python "PrimaryRhs"],

      def "PrimaryRhs" $ union [
        "project">: python "Name",
        "genexp">: python "Genexp",
        "call">: python "Args",
        "slices">: python "Slices"],

-- slices:
--     | slice !','
--     | ','.(slice | starred_expression)+ [',']

      def "Slices" $ record [
        "head">: python "Slice",
        "tail">: list $ python "SliceOrStarredExpression"],

      def "SliceOrStarredExpression" $ union [
        "slice">: python "Slice",
        "starred">: python "StarredExpression"],

-- slice:
--     | [expression] ':' [expression] [':' [expression] ]
--     | named_expression

      def "Slice" $ union [
        "named">: python "NamedExpression",
        "slice">: python "SliceExpression"],

      def "SliceExpression" $ record [
        "start">: optional $ python "Expression",
        "stop">: optional $ python "Expression",
        "step">: optional $ python "Expression"],

-- atom:
--     | NAME
--     | 'True'
--     | 'False'
--     | 'None'
--     | strings
--     | NUMBER
--     | (tuple | group | genexp)
--     | (list | listcomp)
--     | (dict | set | dictcomp | setcomp)
--     | '...'

      def "Atom" $ union [
        "name">: python "Name",
        "true">: unit,
        "false">: unit,
        "none">: unit,
        "string">: string,
        "number">: python "Number",
        "tuple">: python "Tuple",
        "group">: python "Group",
        "genexp">: python "Genexp",
        "list">: python "List",
        "listcomp">: python "Listcomp",
        "dict">: python "Dict",
        "set">: python "Set",
        "dictcomp">: python "Dictcomp",
        "setcomp">: python "Setcomp",
        "ellipsis">: unit],

-- group:
--     | '(' (yield_expr | named_expression) ')'

      def "Group" $ union [
        "yield">: python "YieldExpression",
        "expression">: python "NamedExpression"],

-- # Lambda functions
-- # ----------------
--
-- lambdef:
--     | 'lambda' [lambda_params] ':' expression

      def "Lambda" $ record [
        "params">: python "LambdaParameters",
        "body">: python "Expression"],

-- lambda_params:
--     | lambda_parameters
--
-- # lambda_parameters etc. duplicates parameters but without annotations
-- # or type comments, and if there's no comma after a parameter, we expect
-- # a colon, not a close parenthesis.  (For more, see parameters above.)
-- #
-- lambda_parameters:
--     | lambda_slash_no_default lambda_param_no_default* lambda_param_with_default* [lambda_star_etc]
--     | lambda_slash_with_default lambda_param_with_default* [lambda_star_etc]
--     | lambda_param_no_default+ lambda_param_with_default* [lambda_star_etc]
--     | lambda_param_with_default+ [lambda_star_etc]
--     | lambda_star_etc

        def "LambdaParameters" $ record [
          "slashNoDefault">: optional $ python "LambdaSlashNoDefault",
          "paramNoDefault">: list $ python "LambdaParamNoDefault",
          "paramWithDefault">: list $ python "LambdaParamWithDefault",
          "starEtc">: optional $ python "LambdaStarEtc"],

-- lambda_slash_no_default:
--     | lambda_param_no_default+ '/' ','
--     | lambda_param_no_default+ '/' &':'

        def "LambdaSlashNoDefault" $ record [
            "parameters">: list $ python "LambdaParamNoDefault"],

-- lambda_slash_with_default:
--     | lambda_param_no_default* lambda_param_with_default+ '/' ','
--     | lambda_param_no_default* lambda_param_with_default+ '/' &':'

        def "LambdaSlashWithDefault" $ record [
            "paramNoDefault">: list $ python "LambdaParamNoDefault",
            "paramWithDefault">: nonemptyList $ python "LambdaParamWithDefault"],

-- lambda_star_etc:
--     | '*' lambda_param_no_default lambda_param_maybe_default* [lambda_kwds]
--     | '*' ',' lambda_param_maybe_default+ [lambda_kwds]
--     | lambda_kwds

        def "LambdaStarEtc" $ union [
            "star">: boolean,
            "paramNoDefault">: optional $ python "LambdaParamNoDefault",
            "paramMaybeDefault">: list $ python "LambdaParamMaybeDefault",
            "kwds">: python "LambdaKwds"],

-- lambda_kwds:
--     | '**' lambda_param_no_default

        def "LambdaKwds" $ python "LambdaParamNoDefault",

-- lambda_param_no_default:
--     | lambda_param ','
--     | lambda_param &':'

      def "LambdaParamNoDefault" $ python "Name",

-- lambda_param_with_default:
--     | lambda_param default ','
--     | lambda_param default &':'

      def "LambdaParamWithDefault" $ record [
        "param">: python "Name",
        "default">: python "Default"],

-- lambda_param_maybe_default:
--     | lambda_param default? ','
--     | lambda_param default? &':'

      def "LambdaParamMaybeDefault" $ record [
        "param">: python "Name",
        "default">: optional $ python "Default"],

-- lambda_param: NAME
--
-- # LITERALS
-- # ========
--
-- fstring_middle:
--     | fstring_replacement_field
--     | FSTRING_MIDDLE
-- fstring_replacement_field:
--     | '{' annotated_rhs '='? [fstring_conversion] [fstring_full_format_spec] '}'
-- fstring_conversion:
--     | "!" NAME
-- fstring_full_format_spec:
--     | ':' fstring_format_spec*
-- fstring_format_spec:
--     | FSTRING_MIDDLE
--     | fstring_replacement_field
-- fstring:
--     | FSTRING_START fstring_middle* FSTRING_END
--
-- string: STRING
-- strings: (fstring|string)+
--
-- list:
--     | '[' [star_named_expressions] ']'

      def "List" $ list $ python "StarNamedExpression",

-- tuple:
--     | '(' [star_named_expression ',' [star_named_expressions]  ] ')'

      def "Tuple" $ list $ python "StarNamedExpression",

-- set: '{' star_named_expressions '}'

      def "Set" $ nonemptyList $ python "StarNamedExpression",

-- # Dicts
-- # -----
--
-- dict:
--     | '{' [double_starred_kvpairs] '}'

      def "Dict" $ list $ python "DoubleStarredKvpair",

-- double_starred_kvpairs: ','.double_starred_kvpair+ [',']
--
-- double_starred_kvpair:
--     | '**' bitwise_or
--     | kvpair

      def "DoubleStarredKvpair" $ union [
        "starred">: python "BitwiseOr",
        "pair">: python "Kvpair"],

-- kvpair: expression ':' expression

      def "Kvpair" $ record [
        "key">: python "Expression",
        "value">: python "Expression"],

-- # Comprehensions & Generators
-- # ---------------------------
--
-- for_if_clauses:
--     | for_if_clause+

      def "ForIfClauses" $ nonemptyList $ python "ForIfClause",

-- for_if_clause:
--     | 'async' 'for' star_targets 'in' ~ disjunction ('if' disjunction )*
--     | 'for' star_targets 'in' ~ disjunction ('if' disjunction )*

      def "ForIfClause" $ record [
        "async">: boolean,
        "targets">: nonemptyList $ python "StarTarget",
        "in">: python "Disjunction",
        "ifs">: list $ python "Disjunction"],

-- listcomp:
--     | '[' named_expression for_if_clauses ']'

      def "Listcomp" $ record [
        "expression">: python "NamedExpression",
        "forIfClauses">: python "ForIfClauses"],

-- setcomp:
--     | '{' named_expression for_if_clauses '}'

      def "Setcomp" $ record [
        "expression">: python "NamedExpression",
        "forIfClauses">: python "ForIfClauses"],

-- genexp:
--     | '(' ( assignment_expression | expression !':=') for_if_clauses ')'

      def "Genexp" $ record [
        "head">: python "GenexpHead",
        "tail">: python "ForIfClauses"],

      def "GenexpHead" $ union [
        "assignment">: python "AssignmentExpression",
        "expression">: python "Expression"],

-- dictcomp:
--     | '{' kvpair for_if_clauses '}'

      def "Dictcomp" $ record [
        "kvpair">: python "Kvpair",
        "forIfClauses">: python "ForIfClauses"],

-- # FUNCTION CALL ARGUMENTS
-- # =======================
--
-- arguments:
--     | args [','] &')'
--
-- args:
--     | ','.(starred_expression | ( assignment_expression | expression !':=') !'=')+ [',' kwargs ]
--     | kwargs

      def "Args" $ record [
        "positional">: list $ python "PosArg",
        "kwargOrStarred">: list $ python "KwargOrStarred",
        "kwargOrDoubleStarred">: list $ python "KwargOrDoubleStarred"],

      def "PosArg" $ union [
        "starred">: python "StarredExpression",
        "assignment">: python "AssignmentExpression",
        "expression">: python "Expression"],

-- kwargs:
--     | ','.kwarg_or_starred+ ',' ','.kwarg_or_double_starred+
--     | ','.kwarg_or_starred+
--     | ','.kwarg_or_double_starred+
--
-- starred_expression:
--     | '*' expression

      def "StarredExpression" $ python "Expression",

-- kwarg_or_starred:
--     | NAME '=' expression
--     | starred_expression

      def "KwargOrStarred" $ union [
        "kwarg">: python "Kwarg",
        "starred">: python "StarredExpression"],

      def "Kwarg" $ record [
        "name">: python "Name",
        "value">: python "Expression"],

-- kwarg_or_double_starred:
--     | NAME '=' expression
--     | '**' expression

      def "KwargOrDoubleStarred" $ union [
        "kwarg">: python "Kwarg",
        "doubleStarred">: python "Expression"],

-- # ASSIGNMENT TARGETS
-- # ==================
--
-- # Generic targets
-- # ---------------
--
-- # NOTE: star_targets may contain *bitwise_or, targets may not.
-- star_targets:
--     | star_target !','
--     | star_target (',' star_target )* [',']
--
-- star_targets_list_seq: ','.star_target+ [',']

      def "StarTargetsListSeq" $ nonemptyList $ python "StarTarget",

-- star_targets_tuple_seq:
--     | star_target (',' star_target )+ [',']
--     | star_target ','

      def "StarTargetsTupleSeq" $ nonemptyList $ python "StarTarget",

-- star_target:
--     | '*' (!'*' star_target)
--     | target_with_star_atom

      def "StarTarget" $ union [
        "starred">: python "StarTarget",
        "unstarred">: python "TargetWithStarAtom"],

-- target_with_star_atom:
--     | t_primary '.' NAME !t_lookahead
--     | t_primary '[' slices ']' !t_lookahead
--     | star_atom

      def "TargetWithStarAtom" $ union [
        "project">: python "TPrimaryAndName",
        "slices">: python "TPrimaryAndSlices",
        "atom">: python "StarAtom"],

      def "TPrimaryAndName" $ record [
        "primary">: python "TPrimary",
        "name">: python "Name"],

      def "TPrimaryAndSlices" $ record [
        "primary">: python "TPrimary",
        "slices">: python "Slices"],

-- star_atom:
--     | NAME
--     | '(' target_with_star_atom ')'
--     | '(' [star_targets_tuple_seq] ')'
--     | '[' [star_targets_list_seq] ']'

      def "StarAtom" $ union [
        "name">: python "Name",
        "targetWithStarAtom">: python "TargetWithStarAtom",
        "starTargetsTupleSeq">: optional $ python "StarTargetsTupleSeq",
        "starTargetsListSeq">: optional $ python "StarTargetsListSeq"],

-- single_target:
--     | single_subscript_attribute_target
--     | NAME
--     | '(' single_target ')'

      def "SingleTarget" $ union [
        "subscriptAttributeTarget">: python "SingleSubscriptAttributeTarget",
        "name">: python "Name",
        "parens">: python "SingleTarget"],

-- single_subscript_attribute_target:
--     | t_primary '.' NAME !t_lookahead
--     | t_primary '[' slices ']' !t_lookahead

      def "SingleSubscriptAttributeTarget" $ union [
        "primaryAndName">: python "TPrimaryAndName",
        "primaryAndSlices">: python "TPrimaryAndSlices"],

-- t_primary:
--     | t_primary '.' NAME &t_lookahead
--     | t_primary '[' slices ']' &t_lookahead
--     | t_primary genexp &t_lookahead
--     | t_primary '(' [arguments] ')' &t_lookahead
--     | atom &t_lookahead

      def "TPrimary" $ union [
        "primaryAndName">: python "TPrimaryAndName",
        "primaryAndSlices">: python "TPrimaryAndSlices",
        "primaryAndGenexp">: python "TPrimaryAndGenexp",
        "primaryAndArguments">: python "TPrimaryAndArguments",
        "atom">: python "Atom"],

      def "TPrimaryAndGenexp" $ record [
        "primary">: python "TPrimary",
        "genexp">: python "Genexp"],

      def "TPrimaryAndArguments" $ record [
        "primary">: python "TPrimary",
        "arguments">: optional $ python "Args"],

-- t_lookahead: '(' | '[' | '.'
--
-- # Targets for del statements
-- # --------------------------
--
-- del_targets: ','.del_target+ [',']

      def "DelTargets" $ nonemptyList $ python "DelTarget",

-- del_target:
--     | t_primary '.' NAME !t_lookahead
--     | t_primary '[' slices ']' !t_lookahead
--     | del_t_atom

      def "DelTarget" $ union [
        "primaryAndName">: python "TPrimaryAndName",
        "primaryAndSlices">: python "TPrimaryAndSlices",
        "delTAtom">: python "DelTAtom"],

-- del_t_atom:
--     | NAME
--     | '(' del_target ')'
--     | '(' [del_targets] ')'
--     | '[' [del_targets] ']'

      def "DelTAtom" $ union [
        "name">: python "Name",
        "target">: python "DelTarget",
        "targets">: python "DelTargets"],

-- # TYPING ELEMENTS
-- # ---------------
--
-- # type_expressions allow */** but ignore them
-- type_expressions:
--     | ','.expression+ ',' '*' expression ',' '**' expression
--     | ','.expression+ ',' '*' expression
--     | ','.expression+ ',' '**' expression
--     | '*' expression ',' '**' expression
--     | '*' expression
--     | '**' expression
--     | ','.expression+

      def "TypeExpression" $ union [
        "expression">: python "Expression",
        "starredExpression">: python "Expression",
        "doubleStarredExpression">: python "Expression"],

-- func_type_comment:
--     | NEWLINE TYPE_COMMENT &(NEWLINE INDENT)   # Must be followed by indented block
--     | TYPE_COMMENT

      def "FuncTypeComment" $ python "TypeComment"]