{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Langs.Sql.Ansi where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Grammars
import Hydra.Tools.GrammarToModule
import qualified Hydra.Dsl.Annotations as Ann
import qualified Hydra.Grammar as G

import qualified Data.List as L


sqlModule :: Module
sqlModule = grammarToModule ns sqlGrammar $
    Just ("A subset of ANSI SQL:2003, capturing selected productions of the BNF grammar provided at "
      ++ "https://ronsavage.github.io/SQL/sql-2003-2.bnf.html, which is based on "
      ++ "the Final Committee Draft (FCD) of ISO/IEC 9075-2:2003")
  where
    ns = Namespace "hydra/langs/sql/ansi"

sqlGrammar :: G.Grammar
sqlGrammar = G.Grammar $ tokens ++ productions

tokens :: [G.Production]
tokens = [
    -- <approximate numeric literal>    ::=   <mantissa> E <exponent>
    define "ApproximateNumericLiteral" [regex $ mantissa ++ "E" ++ exponent],

    -- <binary string literal>    ::=
    --         X <quote> [ { <hexit> <hexit> }... ] <quote>
    --         [ { <separator> <quote> [ { <hexit> <hexit> }... ] <quote> }... ]
    --         [ ESCAPE <escape character> ]
    define "BinaryStringLiteral" unsupported,

    -- <character string literal>    ::=
    --         [ <introducer> <character set specification> ]
    --         <quote> [ <character representation> ... ] <quote>
    --         [ { <separator> <quote> [ <character representation> ... ] <quote> }... ]
    define "CharacterStringLiteral" [regex $
      opt(introducer ++ characterSetSpecification)
      ++ quote ++ star(characterRepresentation) ++ quote
      ++ star(separator ++ quote ++ star(characterRepresentation) ++ quote)],

    -- <column name>    ::=   <identifier>
    define "ColumnName" [regex identifier],

    -- <date string>    ::=   <quote> <unquoted date string> <quote>
    define "DateString" unsupported,

    -- <domain name>    ::=   <schema qualified name>
    define "DomainName" [regex schemaQualifiedName],

    -- <exact numeric literal>    ::=
         --         <unsigned integer> [ <period> [ <unsigned integer> ] ]
         --     |     <period> <unsigned integer>
    define "ExactNumericLiteral" [regex $ or [
      unsignedInteger ++ opt (period ++ unsignedInteger),
      period ++ unsignedInteger]],

    -- <left bracket or trigraph>    ::=   <left bracket> | <left bracket trigraph>
    define "LeftBracketOrTrigraph" [regex $ or [leftBracket, leftBracketTrigraph]],

    -- <right bracket or trigraph>    ::=   <right bracket> | <right bracket trigraph>
    define "RightBracketOrTrigraph" [regex $ or [rightBracket, rightBracketTrigraph]],

    -- <national character string literal>    ::=
    --         N <quote> [ <character representation> ... ] <quote>
    --         [ { <separator> <quote> [ <character representation> ... ] <quote> }... ]
    define "NationalCharacterStringLiteral" unsupported,

    -- <path-resolved user-defined type name>    ::=   <user-defined type name>
    define "PathResolvedUserDefinedTypeName" [regex userDefinedTypeName],

    -- <table name>    ::=   <local or schema qualified name>
    define "TableName" [regex localOrSchemaQualifiedName],

    -- <time string>    ::=   <quote> <unquoted time string> <quote>
    define "TimeString" unsupported,

    -- <timestamp string>    ::=   <quote> <unquoted timestamp string> <quote>
    define "TimestampLiteral" unsupported,

    -- <Unicode character string literal>    ::=
    --         [ <introducer> <character set specification> ]
    --         U <ampersand> <quote> [ <Unicode representation> ... ] <quote>
    --         [ { <separator> <quote> [ <Unicode representation> ... ] <quote> }... ]
    --         [ ESCAPE <escape character> ]
    define "UnicodeCharacterStringLiteral" unsupported,

    -- <unsigned integer>    ::=   <digit> ...
    define "UnsignedInteger" [regex unsignedInteger]]
  where
    opt pat = par pat ++ "?"
    or pats = par $ L.intercalate "|" (par <$> pats)
    par pat = "(" ++ pat ++ ")"
    plus pat = par pat ++ "+"
    star pat = par pat ++ "*"

    -- <actual identifier>    ::=   <regular identifier> | <delimited identifier>
    actualIdentifier = regularIdentifier -- Note: this is a simplification

    -- <asterisk>    ::=   *
    asterisk = "*"

    -- <bracketed comment>    ::=
    --         <bracketed comment introducer> <bracketed comment contents> <bracketed comment terminator>
    bracketedComment = bracketedCommentIntroducer ++ bracketedCommentContents ++ bracketedCommentTerminator

    -- <bracketed comment contents>    ::=   [ { <comment character> | <separator> }... ]
    bracketedCommentContents = star $ or [commentCharacter, separator]

    -- <bracketed comment introducer>    ::=   <slash> <asterisk>
    bracketedCommentIntroducer = slash ++ asterisk

    -- <bracketed comment terminator>    ::=   <asterisk> <slash>
    bracketedCommentTerminator = asterisk ++ slash

    -- <catalog name>    ::=   <identifier>
    catalogName = identifier

    -- <character representation>    ::=   <nonquote character> | <quote symbol>
    characterRepresentation = or [nonquoteCharacter, quoteSymbol]

    -- <character set specification>    ::=
    --         <standard character set name>
    --     |     <implementation-defined character set name>
    --     |     <user-defined character set name>
    characterSetSpecification = "" -- TODO

    -- <comment>    ::=   <simple comment> | <bracketed comment>
    comment = or[simpleComment, bracketedComment]

    -- <comment character>    ::=   <nonquote character> | <quote>
    commentCharacter = or [nonquoteCharacter, quote]

    -- <digit>    ::=   0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
    digit = "[0-9]"

    -- <exact numeric literal>    ::=
    --         <unsigned integer> [ <period> [ <unsigned integer> ] ]
    --     |     <period> <unsigned integer>
    exactNumericLiteral = or [
      unsignedInteger ++ opt (period ++ opt unsignedInteger),
      period ++ unsignedInteger]

    -- <exponent>    ::=   <signed integer>
    exponent = signedInteger

    -- <identifier>    ::=   <actual identifier>
    identifier = actualIdentifier

    -- <identifier body>    ::=   <identifier start> [ <identifier part> ... ]
    identifierBody = identifierStart ++ star identifierPart

    -- <identifier extend>    ::=   !! See the Syntax Rules.
    identifierExtend = "[0-9_]" -- TODO

    -- <identifier part>    ::=   <identifier start> | <identifier extend>
    identifierPart = or [identifierStart, identifierExtend]

    -- <identifier start>    ::=   !! See the Syntax Rules.
    identifierStart = "[A-Za-z]" -- TODO

    -- <introducer>    ::=   <underscore>
    introducer = underscore

    -- <left bracket>    ::=   [
    leftBracket = "["

    -- <left bracket trigraph>    ::=   ??(
    leftBracketTrigraph = "??("

    -- <local or schema qualifier>    ::=   <schema name> | MODULE
    localOrSchemaQualifier = or [schemaName, "MODULE"]

    -- <local or schema qualified name>    ::=   [ <local or schema qualifier> <period> ] <qualified identifier>
    localOrSchemaQualifiedName = opt (localOrSchemaQualifier ++ period) ++ qualifiedIdentifier

    -- <mantissa>    ::=   <exact numeric literal>
    mantissa = exactNumericLiteral

    -- <minus sign>    ::=   -
    minusSign = "-"

    -- <newline>    ::=   !! See the Syntax Rules.
    newline = "[\\n]" -- TODO

    -- <nonquote character>    ::=   !! See the Syntax Rules.
    nonquoteCharacter = "[ -&(-~]" -- TODO

    -- <period>    ::=   .
    period = "[.]"

    -- <plus sign>    ::=   +
    plusSign = "+"

    -- <quote>    ::=   '
    quote = "'"

    -- <quote symbol>    ::=   <quote> <quote>
    quoteSymbol = quote ++ quote

    -- <qualified identifier>    ::=   <identifier>
    qualifiedIdentifier = identifier

    -- <regular identifier>    ::=   <identifier body>
    regularIdentifier = identifierBody

    -- <right bracket>    ::=   ]
    rightBracket = "]"

    -- <right bracket trigraph>    ::=   ??)
    rightBracketTrigraph = "??)"

    -- <separator>    ::=   { <comment> | <white space> }...
    separator = star(or[comment, whiteSpace])

    -- <schema name>    ::=   [ <catalog name> <period> ] <unqualified schema name>
    schemaName = opt (catalogName ++ period) ++ unqualifiedSchemaName

    -- <schema qualified name>    ::=   [ <schema name> <period> ] <qualified identifier>
    schemaQualifiedName = opt (schemaName ++ period) ++ qualifiedIdentifier

    -- <schema qualified type name>    ::=   [ <schema name> <period> ] <qualified identifier>
    schemaQualifiedTypeName = opt (schemaName ++ period) ++ qualifiedIdentifier

    -- <sign>    ::=   <plus sign> | <minus sign>
    sign = or [plusSign, minusSign]

    -- <signed integer>    ::=   [ <sign> ] <unsigned integer>
    signedInteger = opt sign ++ unsignedInteger

    -- <simple comment>    ::=   <simple comment introducer> [ <comment character> ... ] <newline>
    simpleComment = simpleCommentIntroducer ++ star(commentCharacter) ++ newline

    -- <simple comment introducer>    ::=   <minus sign> <minus sign> [ <minus sign> ... ]
    simpleCommentIntroducer = minusSign ++ plus(minusSign)

    slash = "/"

    -- <underscore>    ::=   _
    underscore = "_"

    -- <unqualified schema name> ::= <schema name>
    unqualifiedSchemaName = schemaName

    -- <unsigned integer>    ::=   <digit> ...
    unsignedInteger = plus digit

    -- <user-defined type name>    ::=   <schema qualified type name>
    userDefinedTypeName = schemaQualifiedTypeName

    whiteSpace = "[ \\t]" -- TODO

productions :: [G.Production]
productions = [
  -- <approximate numeric type>    ::=
       --         FLOAT [ <left paren> <precision> <right paren> ]
       --     |     REAL
       --     |     DOUBLE PRECISION
  define "ApproximateNumericType" [
    "float">: list[float_, opt(parens["Precision"])],
    "real">: real_,
    "double">: double_precision_],

  -- <array element>    ::=   <value expression>
  define "ArrayElement" [
    "ValueExpression"],

  -- <array element list>    ::=   <array element> [ { <comma> <array element> }... ]
  define "ArrayElementList" [commaList "ArrayElement"],

  -- <array element reference>    ::=
  --         <array value expression> <left bracket or trigraph> <numeric value expression> <right bracket or trigraph>
  define "ArrayElementReference" unsupported,

  -- <array type>    ::=   <data type> ARRAY [ <left bracket or trigraph> <unsigned integer> <right bracket or trigraph> ]
  define "ArrayType" unsupported,

  -- <array value constructor>    ::=
  --         <array value constructor by enumeration>
  --     |     <array value constructor by query>
  define "ArrayValueConstructor" [
    "enumeration">: "ArrayValueConstructorByEnumeration",
    "query">: "ArrayValueConstructorByQuery"],

  -- <array value constructor by query>    ::=
  --         ARRAY <left paren> <query expression> [ <order by clause> ] <right paren>
  define "ArrayValueConstructorByQuery" unsupported,

  -- <array value constructor by enumeration>    ::=
  --         ARRAY <left bracket or trigraph> <array element list> <right bracket or trigraph>
  define "ArrayValueConstructorByEnumeration" [
    list[array_, "LeftBracketOrTrigraph", "ArrayElementList", "RightBracketOrTrigraph"]],

  -- <array value expression>    ::=   <array concatenation> | <array factor>
  define "ArrayValueExpression" unsupported,

  -- <as subquery clause>    ::=   [ <left paren> <column name list> <right paren> ] AS <subquery> <with or without data>
  define "AsSubqueryClause" unsupported,

  -- <attribute or method reference>    ::=
  --         <value expression primary> <dereference operator> <qualified identifier>
  --         [ <SQL argument list> ]
  define "AttributeOrMethodReference" unsupported,

  -- <binary large object string type>    ::=
  --         BINARY LARGE OBJECT [ <left paren> <large object length> <right paren> ]
  --     |     BLOB [ <left paren> <large object length> <right paren> ]
  define "BinaryLargeObjectStringType" [
    "binary">: list[binary_large_object_, opt(parens["LargeObjectLength"])],
    "blob">: list[blob_, opt(parens["LargeObjectLength"])]],

  -- <boolean factor>    ::=   [ NOT ] <boolean test>
  define "BooleanFactor" [
    list[opt(not_), "BooleanTest"]],

  -- <boolean literal>    ::=   TRUE | FALSE | UNKNOWN
  define "BooleanLiteral" [
    true_,
    false_,
    unknown_],

  -- <boolean predicand>    ::=
  --         <parenthesized boolean value expression>
  --     |     <nonparenthesized value expression primary>
  define "BooleanPredicand" unsupported,

  -- <boolean primary>    ::=   <predicate> | <boolean predicand>
  define "BooleanPrimary" [
    "predicate">: "Predicate",
    "predicand">: "BooleanPredicand"],

  -- <boolean term>    ::=
  --         <boolean factor>
  --     |     <boolean term> AND <boolean factor>
  define "BooleanTerm" [
    "factor">: "BooleanFactor",
    "and">: list[
      "lhs">: "BooleanTerm",
      and_,
      "rhs">: "BooleanFactor"]],

  -- <boolean test>    ::=   <boolean primary> [ IS [ NOT ] <truth value> ]
  define "BooleanTest" [
    list["BooleanPrimary", opt(list[is_, opt(not_), "TruthValue"])]],

  -- <boolean type>    ::=   BOOLEAN
  define "BooleanType" [
    boolean_],

  -- <boolean value expression>    ::=
  --         <boolean term>
  --     |     <boolean value expression> OR <boolean term>
  define "BooleanValueExpression" [
    "term">: "BooleanTerm",
    "or">: list[
      "lhs">: "BooleanValueExpression",
      or_,
      "rhs">: "BooleanTerm"]],

  -- <case expression>    ::=   <case abbreviation> | <case specification>
  define "CaseExpression" unsupported,

  -- <cast specification>    ::=   CAST <left paren> <cast operand> AS <cast target> <right paren>
  define "CastSpecification" unsupported,

  -- <character set specification>    ::=
  --         <standard character set name>
  --     |     <implementation-defined character set name>
  --     |     <user-defined character set name>
  define "CharacterSetSpecification" unsupported,

  -- <character string type>    ::=
  --         CHARACTER [ <left paren> <length> <right paren> ]
  --     |     CHAR [ <left paren> <length> <right paren> ]
  --     |     CHARACTER VARYING <left paren> <length> <right paren>
  --     |     CHAR VARYING <left paren> <length> <right paren>
  --     |     VARCHAR <left paren> <length> <right paren>
  --     |     CHARACTER LARGE OBJECT [ <left paren> <large object length> <right paren> ]
  --     |     CHAR LARGE OBJECT [ <left paren> <large object length> <right paren> ]
  --     |     CLOB [ <left paren> <large object length> <right paren> ]
  define "CharacterStringType" [
    "character">: list[character_, opt(parens["Length"])],
    "char">: list[char_, opt(parens["Length"])],
    "characterVarying">: list[character_varying_, left_paren_, "Length", right_paren_],
    "charVarying">: list[char_varying_, left_paren_, "Length", right_paren_],
    "varchar">: list[varchar_, left_paren_, "Length", right_paren_],
    "characterLargeObject">: list[character_large_object_, opt(parens["LargeObjectLength"])],
    "charLargeObject">: list[char_large_object_, opt(parens["LargeObjectLength"])],
    "clob">: list[clob_, opt(parens["LargeObjectLength"])]],

  -- <collate clause>    ::=   COLLATE <collation name>
  define "CollateClause" unsupported,

  -- <collection type>    ::=   <array type> | <multiset type>
  define "CollectionType" [
    "array">: "ArrayType",
    "multiset">: "MultisetType"],

  -- <collection value constructor>    ::=   <array value constructor> | <multiset value constructor>
  define "CollectionValueConstructor" [
    "array">: "ArrayValueConstructor",
    "multiset">: "MultisetValueConstructor"],

  -- <collection value expression>    ::=   <array value expression> | <multiset value expression>
  define "CollectionValueExpression" [
    "array">: "ArrayValueExpression",
    "multiset">: "MultisetValueExpression"],

  -- <column constraint definition>    ::=   [ <constraint name definition> ] <column constraint> [ <constraint characteristics> ]
  define "ColumnConstraintDefinition" unsupported,

  -- <column definition>    ::=
  --         <column name> [ <data type> | <domain name> ] [ <reference scope check> ]
  --         [ <default clause> | <identity column specification> | <generation clause> ]
  --         [ <column constraint definition> ... ] [ <collate clause> ]
  define "ColumnDefinition" [
    list[
      "name">: "ColumnName",
      "typeOrDomain">: opt(alts["DataType", "DomainName"]),
      "refScope">: opt"ReferenceScopeCheck",
      "defaultOrIdentityOrGeneration">: opt(alts["DefaultClause", "IdentityColumnSpecification", "GenerationClause"]),
      "constraints">: star"ColumnConstraintDefinition",
      "collate">: opt"CollateClause"]],

  -- <column name list>    ::=   <column name> [ { <comma> <column name> }... ]
  define "ColumnNameList" [commaList "ColumnName"],

  -- <column options>    ::=   <column name> WITH OPTIONS <column option list>
  define "ColumnOptions" unsupported,

  -- <column reference>    ::=
       --         <basic identifier chain>
       --     |     MODULE <period> <qualified identifier> <period> <column name>
  define "ColumnReference" unsupported,

  -- <common value expression>    ::=
  --         <numeric value expression>
  --     |     <string value expression>
  --     |     <datetime value expression>
  --     |     <interval value expression>
  --     |     <user-defined type value expression>
  --     |     <reference value expression>
  --     |     <collection value expression>
  define "CommonValueExpression" [
    "numeric">: "NumericValueExpression",
    "string">: "StringValueExpression",
    "datetime">: "DatetimeValueExpression",
    "interval">: "IntervalValueExpression",
    "userDefined">: "UserDefinedTypeValueExpression",
    "reference">: "ReferenceValueExpression",
    "collection">: "CollectionValueExpression"],

  -- <contextually typed row value expression>    ::=
  --         <row value special case>
  --     |     <contextually typed row value constructor>
  define "ContextuallyTypedRowValueExpression" [
    "specialCase">: "RowValueSpecialCase",
    "constructor">: "ContextuallyTypedRowValueConstructor"],

  -- <contextually typed row value constructor>    ::=
  --         <common value expression>
  --     |     <boolean value expression>
  --     |     <contextually typed value specification>
  --     |     <left paren> <contextually typed row value constructor element> <comma> <contextually typed row value constructor element list> <right paren>
  --     |     ROW <left paren> <contextually typed row value constructor element list> <right paren>
  define "ContextuallyTypedRowValueConstructor" unsupported,

  -- <contextually typed row value expression list>    ::=   <contextually typed row value expression> [ { <comma> <contextually typed row value expression> }... ]
  define "ContextuallyTypedRowValueExpressionList" [commaList "ContextuallyTypedRowValueExpression"],

  -- <contextually typed table value constructor>    ::=   VALUES <contextually typed row value expression list>
  define "ContextuallyTypedTableValueConstructor" [
    list[values_, "ContextuallyTypedRowValueExpressionList"]],

  -- <data type>    ::=
  --         <predefined type>
  --     |     <row type>
  --     |     <path-resolved user-defined type name>
  --     |     <reference type>
  --     |     <collection type>
  define "DataType" [
    "predefined">: "PredefinedType",
    "row">: "RowType",
    "named">: "PathResolvedUserDefinedTypeName",
    "reference">: "ReferenceType",
    "collection">: "CollectionType"],

  -- <date literal>    ::=   DATE <date string>
  define "DateLiteral" [
    list[date_, "DateString"]],

  -- <datetime literal>    ::=   <date literal> | <time literal> | <timestamp literal>
  define "DatetimeLiteral" [
    "date">: "DateLiteral",
    "time">: "TimeLiteral",
    "timestamp">: "TimestampLiteral"],

  -- <datetime type>    ::=
  --         DATE
  --     |     TIME [ <left paren> <time precision> <right paren> ] [ <with or without time zone> ]
  --     |     TIMESTAMP [ <left paren> <timestamp precision> <right paren> ] [ <with or without time zone> ]
  define "DatetimeType" unsupported,

  -- <datetime value expression>    ::=
  --         <datetime term>
  --     |     <interval value expression> <plus sign> <datetime term>
  --     |     <datetime value expression> <plus sign> <interval term>
  --     |     <datetime value expression> <minus sign> <interval term>
  define "DatetimeValueExpression" unsupported,

  -- <default clause>    ::=   DEFAULT <default option>
  define "DefaultClause" unsupported,

  -- <exact numeric type>    ::=
  --         NUMERIC [ <left paren> <precision> [ <comma> <scale> ] <right paren> ]
  --     |     DECIMAL [ <left paren> <precision> [ <comma> <scale> ] <right paren> ]
  --     |     DEC [ <left paren> <precision> [ <comma> <scale> ] <right paren> ]
  --     |     SMALLINT
  --     |     INTEGER
  --     |     INT
  --     |     BIGINT
  define "ExactNumericType" [
    "numeric">: list[numeric_, opt(parens["Precision", opt(list[comma_, "Scale"])])],
    "decimal">: list[decimal_, opt(parens["Precision", opt(list[comma_, "Scale"])])],
    "dec">: list[dec_, opt(parens["Precision", opt(list[comma_, "Scale"])])],
    "smallint">: smallint_,
    "integer">: integer_,
    "int">: int_,
    "bigint">: bigint_],

  -- <field reference>    ::=   <value expression primary> <period> <field name>
  define "FieldReference" unsupported,

  -- <from constructor>    ::=
  --         [ <left paren> <insert column list> <right paren> ] [ <override clause> ] <contextually typed table value constructor>
  define "FromConstructor" [
    list[
      "columns">: opt(parens["InsertColumnList"]),
      "override">: opt"OverrideClause",
      "values">: "ContextuallyTypedTableValueConstructor"]],

  -- <from default>    ::=   DEFAULT VALUES
  define "FromDefault" [
    default_values_],

  -- <from subquery>    ::=   [ <left paren> <insert column list> <right paren> ] [ <override clause> ] <query expression>
  define "FromSubquery" unsupported,

  -- <general literal>    ::=
  --         <character string literal>
  --     |     <national character string literal>
  --     |     <Unicode character string literal>
  --     |     <binary string literal>
  --     |     <datetime literal>
  --     |     <interval literal>
  --     |     <boolean literal>
  define "GeneralLiteral" [
    "string">: "CharacterStringLiteral",
    "nationalString">: "NationalCharacterStringLiteral",
    "unicode">: "UnicodeCharacterStringLiteral",
    "binary">: "BinaryStringLiteral",
    "dateTime">: "DatetimeLiteral",
    "interval">: "IntervalLiteral",
    "boolean">: "BooleanLiteral"],

  -- <general value specification>    ::=
       --         <host parameter specification>
       --     |     <SQL parameter reference>
       --     |     <dynamic parameter specification>
       --     |     <embedded variable specification>
       --     |     <current collation specification>
       --     |     CURRENT_DEFAULT_TRANSFORM_GROUP
       --     |     CURRENT_PATH
       --     |     CURRENT_ROLE
       --     |     CURRENT_TRANSFORM_GROUP_FOR_TYPE <path-resolved user-defined type name>
       --     |     CURRENT_USER
       --     |     SESSION_USER
       --     |     SYSTEM_USER
       --     |     USER
       --     |     VALUE
  define "GeneralValueSpecification" unsupported,

  -- <generation clause>    ::=   <generation rule> AS <generation expression>
  define "GenerationClause" unsupported,

  -- <global or local>    ::=   GLOBAL | LOCAL
  define "GlobalOrLocal" [
    "global">: global_,
    "local">: local_],

  -- <identity column specification>    ::=
  --         GENERATED { ALWAYS | BY DEFAULT } AS IDENTITY
  --         [ <left paren> <common sequence generator options> <right paren> ]
  define "IdentityColumnSpecification" unsupported,

  -- <insert column list>    ::=   <column name list>
  define "InsertColumnList" [
    "ColumnNameList"],

  -- <insert columns and source>    ::=
  --         <from subquery>
  --     |     <from constructor>
  --     |     <from default>
  define "InsertColumnsAndSource" [
    "subquery">: "FromSubquery",
    "constructor">: "FromConstructor",
    "default">: "FromDefault"],

  -- <insert statement>    ::=   INSERT INTO <insertion target> <insert columns and source>
  define "InsertStatement" [
    list[
      insert_into_,
      "target">: "InsertionTarget",
      "columnsAndSource">: "InsertColumnsAndSource"]],

  -- <insertion target>    ::=   <table name>
  define "InsertionTarget" [
    "TableName"],

  -- <interval literal>    ::=   INTERVAL [ <sign> ] <interval string> <interval qualifier>
  define "IntervalLiteral" unsupported,

  -- <interval type>    ::=   INTERVAL <interval qualifier>
  define "IntervalType" unsupported,

  -- <interval value expression>    ::=
  --         <interval term>
  --     |     <interval value expression 1> <plus sign> <interval term 1>
  --     |     <interval value expression 1> <minus sign> <interval term 1>
  --     |     <left paren> <datetime value expression> <minus sign> <datetime term> <right paren> <interval qualifier>
  define "IntervalValueExpression" unsupported,

  -- <large object length>    ::=
  --         <unsigned integer> [ <multiplier> ] [ <char length units> ]
  --     |     <large object length token> [ <char length units> ]
  define "LargeObjectLength" unsupported,

  -- <length>    ::=   <unsigned integer>
  define "Length" [
      "UnsignedInteger"],

  -- <like clause>    ::=   LIKE <table name> [ <like options> ]
  define "LikeClause" unsupported,

  -- <method invocation>    ::=   <direct invocation> | <generalized invocation>
  define "MethodInvocation" unsupported,

  -- <multiset element reference>    ::=
  --         ELEMENT <left paren> <multiset value expression> <right paren>
  define "MultisetElementReference" unsupported,

  -- <multiset type>    ::=   <data type> MULTISET
  define "MultisetType" [
    list["DataType", multiset_]],

  -- <multiset value constructor>    ::=
  --         <multiset value constructor by enumeration>
  --     |     <multiset value constructor by query>
  --     |     <table value constructor by query>
  define "MultisetValueConstructor" unsupported,

  -- <multiset value expression>    ::=
  --         <multiset term>
  --     |     <multiset value expression> MULTISET UNION [ ALL | DISTINCT ] <multiset term>
  --     |     <multiset value expression> MULTISET EXCEPT [ ALL | DISTINCT ] <multiset term>
  define "MultisetValueExpression" unsupported,

  -- <national character string type>    ::=
  --         NATIONAL CHARACTER [ <left paren> <length> <right paren> ]
  --     |     NATIONAL CHAR [ <left paren> <length> <right paren> ]
  --     |     NCHAR [ <left paren> <length> <right paren> ]
  --     |     NATIONAL CHARACTER VARYING <left paren> <length> <right paren>
  --     |     NATIONAL CHAR VARYING <left paren> <length> <right paren>
  --     |     NCHAR VARYING <left paren> <length> <right paren>
  --     |     NATIONAL CHARACTER LARGE OBJECT [ <left paren> <large object length> <right paren> ]
  --     |     NCHAR LARGE OBJECT [ <left paren> <large object length> <right paren> ]
  --     |     NCLOB [ <left paren> <large object length> <right paren> ]
  define "NationalCharacterStringType" unsupported,

  -- <new specification>    ::=   NEW <routine invocation>
  define "NewSpecification" unsupported,

  -- <next value expression>    ::=   NEXT VALUE FOR <sequence generator name>
  define "NextValueExpression" unsupported,

  -- <numeric type>    ::=   <exact numeric type> | <approximate numeric type>
  define "NumericType" [
    "exact">: "ExactNumericType",
    "approximate">: "ApproximateNumericType"],

  -- <numeric value expression>    ::=
  --         <term>
  --     |     <numeric value expression> <plus sign> <term>
  --     |     <numeric value expression> <minus sign> <term>
  define "NumericValueExpression" unsupported,

  -- <override clause>    ::=   OVERRIDING USER VALUE | OVERRIDING SYSTEM VALUE
  define "OverrideClause" [
    overriding_user_value_,
    overriding_system_value],

  -- <parenthesized value expression>    ::=   <left paren> <value expression> <right paren>
  define "ParenthesizedValueExpression" [
    parens["ValueExpression"]],

  -- <precision>    ::=   <unsigned integer>
  define "Precision" [
    "UnsignedInteger"],

  -- <predefined type>    ::=
  --         <character string type> [ CHARACTER SET <character set specification> ] [ <collate clause> ]
  --     |     <national character string type> [ <collate clause> ]
  --     |     <binary large object string type>
  --     |     <numeric type>
  --     |     <boolean type>
  --     |     <datetime type>
  --     |     <interval type>
  define "PredefinedType" [
    "string">: list[
      "type">: "CharacterStringType",
      "characters">: opt(list[character_set_, "CharacterSetSpecification"]),
      "collate">: opt"CollateClause"],
    "nationalString">: list[
      "type">: "NationalCharacterStringType",
      "collate">: opt"CollateClause"],
    "blob">: "BinaryLargeObjectStringType",
    "numeric">: "NumericType",
    "boolean">: "BooleanType",
    "datetime">: "DatetimeType",
    "interval">: "IntervalType"],

  -- <predicate>    ::=
  --         <comparison predicate>
  --     |     <between predicate>
  --     |     <in predicate>
  --     |     <like predicate>
  --     |     <similar predicate>
  --     |     <null predicate>
  --     |     <quantified comparison predicate>
  --     |     <exists predicate>
  --     |     <unique predicate>
  --     |     <normalized predicate>
  --     |     <match predicate>
  --     |     <overlaps predicate>
  --     |     <distinct predicate>
  --     |     <member predicate>
  --     |     <submultiset predicate>
  --     |     <set predicate>
  --     |     <type predicate>
  define "Predicate" unsupported,

  -- <query expression>    ::=   [ <with clause> ] <query expression body>
  define "QueryExpression" unsupported,

  -- <reference scope check>    ::=   REFERENCES ARE [ NOT ] CHECKED [ ON DELETE <reference scope check action> ]
  define "ReferenceScopeCheck" unsupported,

  -- <reference type>    ::=   REF <left paren> <referenced type> <right paren> [ <scope clause> ]
  define "ReferenceType" unsupported,

  -- <row type>    ::=   ROW <row type body>
  define "RowType" unsupported,

  -- <row value special case>    ::=   <nonparenthesized value expression primary>
  define "RowValueSpecialCase" [
    "NonparenthesizedValueExpressionPrimary"],

  -- <nonparenthesized value expression primary>    ::=
  --         <unsigned value specification>
  --     |     <column reference>
  --     |     <set function specification>
  --     |     <window function>
  --     |     <scalar subquery>
  --     |     <case expression>
  --     |     <cast specification>
  --     |     <field reference>
  --     |     <subtype treatment>
  --     |     <method invocation>
  --     |     <static method invocation>
  --     |     <new specification>
  --     |     <attribute or method reference>
  --     |     <reference resolution>
  --     |     <collection value constructor>
  --     |     <array element reference>
  --     |     <multiset element reference>
  --     |     <routine invocation>
  --     |     <next value expression>
  define "NonparenthesizedValueExpressionPrimary" [
    "unsigned">: "UnsignedValueSpecification",
    "column">: "ColumnReference",
    "setFunction">: "SetFunctionSpecification",
    "windowFunction">: "WindowFunction",
    "scalarSubquery">: "ScalarSubquery",
    "cases">: "CaseExpression",
    "cast">: "CastSpecification",
    "field">: "FieldReference",
    "subtype">: "SubtypeTreatment",
    "method">: "MethodInvocation",
    "staticMethod">: "StaticMethodInvocation",
    "new">: "NewSpecification",
    "attributeOrMethod">: "AttributeOrMethodReference",
    "reference">: "ReferenceResolution",
    "collection">: "CollectionValueConstructor",
    "arrayElement">: "ArrayElementReference",
    "multisetElement">: "MultisetElementReference",
    "routine">: "RoutineInvocation",
    "next">: "NextValueExpression"],

  -- <reference resolution>    ::=   DEREF <left paren> <reference value expression> <right paren>
  define "ReferenceResolution" unsupported,

  -- <reference value expression>    ::=   <value expression primary>
  define "ReferenceValueExpression" [
    "ValueExpressionPrimary"],

  -- <row value expression>    ::=
  --         <row value special case>
  --     |     <explicit row value constructor>
  define "RowValueExpression" unsupported,

  -- <routine invocation>    ::=   <routine name> <SQL argument list>
  define "RoutineInvocation" unsupported,

  -- <scalar subquery>    ::=   <subquery>
  define "ScalarSubquery" [
    "Subquery"],

  -- <scale>    ::=   <unsigned integer>
  define "Scale" [
    "UnsignedInteger"],

  -- <self-referencing column specification>    ::=   REF IS <self-referencing column name> <reference generation>
  define "SelfReferencingColumnSpecification" unsupported,

  -- <set function specification>    ::=   <aggregate function> | <grouping operation>
  define "SetFunctionSpecification" unsupported,

  -- <static method invocation>    ::=
  --         <path-resolved user-defined type name> <double colon> <method name> [ <SQL argument list> ]
  define "StaticMethodInvocation" unsupported,

  -- <string value expression>    ::=   <character value expression> | <blob value expression>
  define "StringValueExpression" unsupported,

  -- <subquery>    ::=   <left paren> <query expression> <right paren>
  define "Subquery" [
    parens["QueryExpression"]],

  -- <subtable clause>    ::=   UNDER <supertable clause>
  define "SubtableClause" unsupported,

  -- <subtype treatment>    ::=
  --         TREAT <left paren> <subtype operand> AS <target subtype> <right paren>
  define "SubtypeTreatment" unsupported,

  -- <table commit action>    ::=   PRESERVE | DELETE
  define "TableCommitAction" [
    "preserve">: preserve_,
    "delete">: delete_],

  -- <table constraint definition>    ::=   [ <constraint name definition> ] <table constraint> [ <constraint characteristics> ]
  define "TableConstraintDefinition" unsupported,

  -- <table contents source>    ::=
  --         <table element list>
  --     |     OF <path-resolved user-defined type name> [ <subtable clause> ] [ <table element list> ]
  --     |     <as subquery clause>
  define "TableContentsSource" [
    "list">: "TableElementList",
    "subtable">: list [
      of_,
      "type">: "PathResolvedUserDefinedTypeName",
      "subtable">: opt"SubtableClause",
      "elements">: opt"TableElementList"],
    "subquery">: "AsSubqueryClause"],

  -- <table definition>    ::=
  --          CREATE [ <table scope> ] TABLE <table name> <table contents source>
  --          [ ON COMMIT <table commit action> ROWS ]
  define "TableDefinition" [
    list[
      create_,
      "scope">: opt"TableScope",
      table_,
      "name">: "TableName",
      "source">: "TableContentsSource",
      "commitActions">: opt(list[on_commit_, "TableCommitAction", rows_])]],

  -- <table element>    ::=
  --         <column definition>
  --     |     <table constraint definition>
  --     |     <like clause>
  --     |     <self-referencing column specification>
  --     |     <column options>
  define "TableElement" [
    "column">: "ColumnDefinition",
    "tableConstraint">: "TableConstraintDefinition",
    "like">: "LikeClause",
    "selfReferencingColumn">: "SelfReferencingColumnSpecification",
    "columOptions">: "ColumnOptions"],

  -- <table element list>    ::=   <left paren> <table element> [ { <comma> <table element> }... ] <right paren>
  define "TableElementList" [
    parens[commaList "TableElement"]],

  -- <table scope>    ::=   <global or local> TEMPORARY
  define "TableScope" [
    list["GlobalOrLocal", temporary_]],

  -- <time literal>    ::=   TIME <time string>
  define "TimeLiteral" [
    list[time_, "TimeString"]],

  define "TruthValue" [
    true_,
    false_,
    unknown_],

  -- <unsigned literal>    ::=   <unsigned numeric literal> | <general literal>
  define "UnsignedLiteral" [
    "numeric">: "UnsignedNumericLiteral",
    "general">: "GeneralLiteral"],

  -- <unsigned numeric literal>    ::=   <exact numeric literal> | <approximate numeric literal>
  define "UnsignedNumericLiteral" [
    "exact">: "ExactNumericLiteral",
    "approximate">: "ApproximateNumericLiteral"],

  -- <unsigned value specification>    ::=   <unsigned literal> | <general value specification>
  define "UnsignedValueSpecification" [
    "literal">: "UnsignedLiteral",
    "general">: "GeneralValueSpecification"],

  -- <user-defined type value expression>    ::=   <value expression primary>
  define "UserDefinedTypeValueExpression" [
    "ValueExpressionPrimary"],

  -- <value expression>    ::=
  --         <common value expression>
  --     |     <boolean value expression>
  --     |     <row value expression>
  define "ValueExpression" [
    "common">: "CommonValueExpression",
    "boolean">: "BooleanValueExpression",
    "row">: "RowValueExpression"],

  -- <value expression primary>    ::=
  --         <parenthesized value expression>
  --     |     <nonparenthesized value expression primary>
  define "ValueExpressionPrimary" [
    "parens">: "ParenthesizedValueExpression",
    "noparens">: "NonparenthesizedValueExpressionPrimary"],

  -- <window function>    ::=   <window function type> OVER <window name or specification>
  define "WindowFunction" unsupported]

and_ = terminal "AND"
array_ = terminal "ARRAY"
bigint_ = terminal "BIGINT"
binary_large_object_ = terminal "BINARY LARGE OBJECT"
blob_ = terminal "BLOB"
boolean_ = terminal "BOOLEAN"
char_ = terminal "CHAR"
char_large_object_ = terminal "CHAR LARGE OBJECT"
char_varying_ = terminal "CHAR VARYING"
character_ = terminal "CHARACTER"
character_large_object_ = terminal "CHARACTER LARGE OBJECT"
character_set_ = terminal "CHARACTER SET"
character_varying_ = terminal "CHARACTER VARYING"
clob_ = terminal "CLOB"
comma_ = terminal ","
create_ = terminal "CREATE"
date_ = terminal "DATE"
dec_ = terminal "DEC"
decimal_ = terminal "DECIMAL"
default_values_ = terminal "DEFAULT VALUES"
delete_ = terminal "DELETE"
double_precision_ = terminal "DOUBLE PRECISION"
false_ = terminal "FALSE"
float_ = terminal "FLOAT"
global_ = terminal "GLOBAL"
insert_into_ = terminal "INSERT INTO"
int_ = terminal "INT"
integer_ = terminal "INTEGER"
is_ = terminal "IS"
left_paren_ = terminal "("
local_ = terminal "LOCAL"
multiset_ = terminal "MULTISET"
numeric_ = terminal "NUMERIC"
of_ = terminal "OF"
not_ = terminal "NOT"
on_commit_ = terminal "ON COMMIT"
or_ = terminal "OR"
overriding_user_value_ = terminal "OVERRIDING USER VALUE"
overriding_system_value = terminal "OVERRIDING SYSTEM VALUE"
preserve_ = terminal "PRESERVE"
real_ = terminal "REAL"
right_paren_ = terminal ")"
rows_ = terminal "ROWS"
smallint_ = terminal "SMALLINT"
table_ = terminal "TABLE"
temporary_ = terminal "TEMPORARY"
time_ = terminal "TIME"
true_ = terminal "TRUE"
unknown_ = terminal "UNKNOWN"
values_ = terminal "VALUES"
varchar_ = terminal "VARCHAR"

commaList pat = list[
  "first">: pat,
  "rest">: star(list[comma_, pat])]
parens ps = list $ [left_paren_] ++ ps ++ [right_paren_]
unsupported = [terminal "unsupported"]
