{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Langs.Shex.Syntax where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Grammars
import Hydra.Tools.GrammarToModule
import qualified Hydra.Dsl.Annotations as Ann
import qualified Hydra.Grammar as G


base_ = terminal "BASE"
prefix_ = terminal "PREFIX"
start_ = terminal "start"
equal_ = terminal "="
or_ = terminal "OR"
and_ = terminal "AND"
not_ = terminal "NOT"
true_ = terminal "true"
false_ = terminal "false"
iri_ = terminal "IRI"
bnode_ = terminal "BNODE"
literal_ = terminal "LITERAL"
nonLiteral_ = terminal "NONLITERAL"
length_ = terminal "LENGTH"
minLength_ = terminal "MINLENGTH"
maxLength_ = terminal "MAXLENGTH"
external_ = terminal "EXTERNAL"
percent_ = terminal "%"
at_ = terminal "@"
dollar_ = terminal "$"
ampersand_ = terminal "&"
colon_ = terminal ":"
period_ = terminal "."
coma_ = terminal ","
semicolon_ = terminal ";"
underscore_ = terminal "_"
dash_ = terminal "-"
parenOpen_ = terminal "("
parenClose_ = terminal ")"
braceOpen_ = terminal "{"
braceClose_ = terminal "}"
pipe_ = terminal "|"
star_ = terminal "*"
plus_ = terminal "+"
question_ = terminal "?"
tilde_ = terminal "~"
doubleFrwSlash_ = terminal "\\"
singleQuote_ = terminal "'"
doubleQuote_ = terminal "\""

minInclusive_ = terminal "MININCLUSIVE"
minExclusive_ = terminal "MINEXCLUSIVE"
maxInclusive_ = terminal "MAXINCLUSIVE"
maxExclusive_ = terminal "MAXEXCLUSIVE"
totalDigits_ = terminal "TOTALDIGITS"
fractionDigits_ = terminal "FRACTIONDIGITS"
extra_ = terminal "EXTRA"
closed_ = terminal "CLOSED"


shexSyntaxModule :: Module
shexSyntaxModule = grammarToModule ns shexGrammar $
    Just ("A Shex model. Based on the BNF at:\n" ++
        "  https://github.com/shexSpec/grammar/blob/master/bnf")
    where
        ns = Namespace "hydra/langs/shex/syntax"

shexGrammar :: G.Grammar
shexGrammar = G.Grammar [

-- [1] ShexDoc ::= Directive* ((NotStartAction | StartActions) Statement*)?
  define "ShexDoc" [
    list[star"Directive", opt(list[ alts["NotStartAction", "StartActions"], star "Statement" ]), "PrefixDecl"]],

-- [2] Directive ::= BaseDecl | PrefixDecl
  define "Directive" [
     "BaseDecl", "PrefixDecl"],

-- [3] BaseDecl ::= "BASE" IriRef
 define "BaseDecl" [
     list[base_, "IriRef"]],

-- [4] PrefixDecl ::= "PREFIX" PnameNs IriRef
 define "PrefixDecl" [
     list[prefix_, "PnameNs", "IriRef"]],

-- [5] NotStartAction ::= start | shapeExprDecl
-- [6] start ::= "start" '=' ShapeExpression
-- [9] shapeExprDecl ::= ShapeExprLabel (ShapeExpression|"EXTERNAL")
  define "NotStartAction" [
    "start">: list[start_, equal_, "ShapeExpression"],
    "shapeExprDecl">: list["ShapeExprLabel", alts["ShapeExpression", external_]]],

-- [7] StartActions ::= CodeDecl+
  define "StartActions" [
    plus("CodeDecl")],

-- [8] Statement ::= Directive | NotStartAction
  define "Statement" [
    alts[ "Directive", "NotStartAction"]],

-- [10] ShapeExpression ::= ShapeOr
  define "ShapeExpression" [
    "ShapeOr"],

-- [11] InlineShapeExpression ::= InlineShapeOr
  define "InlineShapeExpression" [
    "InlineShapeOr"],

-- [12] ShapeOr ::= ShapeAnd ("OR" ShapeAnd)*
  define "ShapeOr" [
    list["ShapeAnd", star(list[or_, "ShapeAnd"])]],

-- [13] InlineShapeOr ::= InlineShapeAnd ("OR" InlineShapeAnd)*
  define "InlineShapeOr" [
    list["ShapeAnd", star(list[or_, "InlineShapeAnd"])]],

-- [14] ShapeAnd ::= ShapeNot ("AND" ShapeNot)*
  define "ShapeAnd" [
    list["ShapeNot", star(list[and_, "ShapeNot"])]],

-- [15] InlineShapeAnd ::= InlineShapeNot ("AND" InlineShapeNot)*
  define "InlineShapeAnd" [
    list["InlineShapeNot", star(list[and_, "InlineShapeNot"])]],

-- [16] ShapeNot ::= "NOT"? ShapeAtom
  define "ShapeNot" [
    list[opt (not_), "ShapeAtom"]],

-- [17] InlineShapeNot ::= "NOT"? InlineShapeAtom
  define "InlineShapeNot" [
    list[opt(not_), "InlineShapeAtom"]],

-- [18] ShapeAtom ::= NodeConstraint ShapeOrRef?
--                                   | ShapeOrRef
--                                   | "(" ShapeExpression ")"
--                                   | '.'  # no constraint
  define "ShapeAtom" [
    list["NodeConstraint", opt("ShapeOrRef")],
    "ShapeOrRef",
    list[parenOpen_, "ShapeExpression", parenClose_],
    period_],

-- [19] InlineShapeAtom ::= NodeConstraint InlineShapeOrRef?
--                                   | InlineShapeOrRef NodeConstraint?
--                                   | "(" ShapeExpression ")"
--                                   | '.'  # no constraint
  define "InlineShapeAtom" [
    list["NodeConstraint", opt("InlineShapeOrRef")],
    list["InlineShapeOrRef", opt("NodeConstraint")],
    list[parenOpen_, "ShapeExpression", parenClose_],
    period_],

-- [20] ShapeOrRef ::= ShapeDefinition
--                                   | AtpNameLn | AtpNameNs | '@' ShapeExprLabel
  define "ShapeOrRef" [
    "ShapeDefinition",
    "AtpNameLn",
    "AtpNameNs",
    list[at_,"ShapeExprLabel"]],

-- [21] InlineShapeOrRef ::= InlineShapeDefinition
--                                   | AtpNameLn | AtpNameNs | '@' ShapeExprLabel
  define "InlineShapeOrRef" [
    "InlineShapeDefinition",
    "AtpNameLn",
    "AtpNameNs",
    list[at_,"ShapeExprLabel"]],

-- [22] NodeConstraint ::= "LITERAL" XsFacet*
--                                   | NonLiteralKind StringFacet*
--                                   | Datatype XsFacet*
--                                   | ValueSet XsFacet*
--                                   | XsFacet+
  define "NodeConstraint" [
    list[literal_, star("XsFacet")],
    list["NonLiteralKind", star("StringFacet")],
    list["Datatype", star("XsFacet")],
    list["ValueSet", star("XsFacet")],
    list["ValueSet", star("XsFacet")],
    plus("XsFacet")],

-- [23] NonLiteralKind ::= "IRI" | "BNODE" | "NONLITERAL"
  define "NonLiteralKind" [iri_, bnode_, nonLiteral_],

-- [24] XsFacet ::= StringFacet | NumericFacet
  define "XsFacet" ["StringFacet", "NumericFacet"],

-- [25] StringFacet ::= StringLength Integer | Regexp
  define "StringFacet" [
    list ["StringLength", "Integer"],
    "Regexp" ],

-- [26] StringLength ::= "LENGTH" | "MINLENGTH" | "MAXLENGTH"
  define "StringLength" [
    length_, minLength_, maxLength_],

-- [27] NumericFacet ::= NumericRange NumericLiteral
--                                   | NumericLength Integer
  define "NumericFacet" [
    list ["NumericRange", "NumericLiteral"],
    list ["NumericLength", "Integer"]],

-- [28] NumericRange ::= "MININCLUSIVE" | "MINEXCLUSIVE" | "MAXINCLUSIVE" | "MAXEXCLUSIVE"
  define "NumericRange" [
    minInclusive_, minExclusive_, maxInclusive_, maxExclusive_],

-- [29] NumericLength ::= "TOTALDIGITS" | "FRACTIONDIGITS"
  define "NumericLength" [
    totalDigits_, fractionDigits_],

-- [30] ShapeDefinition ::= (IncludeSet | ExtraPropertySet | "CLOSED")* '{' TripleExpression? '}' Annotation* SemanticActions
  define "ShapeDefinition" [
    list[star(alts["IncludeSet", "ExtraPropertySet", closed_]),
        braceOpen_, opt("TripleExpression"), braceClose_,
        star("Annotation"), "SemanticActions"]],

-- [31] InlineShapeDefinition ::= (IncludeSet | ExtraPropertySet | "CLOSED")* '{' TripleExpression? '}'
  define "InlineShapeDefinition" [
    list[star(alts["IncludeSet", "ExtraPropertySet", closed_]), braceOpen_, opt("TripleExpression"), braceClose_]],

-- [32] ExtraPropertySet ::= "EXTRA" Predicate+
  define "ExtraPropertySet" [
    list[extra_, plus"Predicate"]],

-- [33] TripleExpression ::= OneOfTripleExpr
  define "TripleExpression" [
    "OneOfTripleExpr"],

-- [34] OneOfTripleExpr ::= GroupTripleExpr | MultiElementOneOf
  define "OneOfTripleExpr" [
    "GroupTripleExpr",
    "MultiElementOneOf"],

-- [35] MultiElementOneOf ::= GroupTripleExpr ('|' GroupTripleExpr)+
  define "MultiElementOneOf" [
    list["GroupTripleExpr", plus(list[pipe_, "GroupTripleExpr"])]],

-- [36] InnerTripleExpr ::= MultiElementGroup | MultiElementOneOf
  define "InnerTripleExpr" [
    "MultiElementGroup",
    "MultiElementOneOf"],

-- [37] GroupTripleExpr ::= SingleElementGroup | MultiElementGroup
  define "GroupTripleExpr" [
    "SingleElementGroup",
    "MultiElementGroup"],

-- [38] SingleElementGroup ::= UnaryTripleExpr ';'?
  define "SingleElementGroup" [
    list["UnaryTripleExpr", opt(semicolon_)]],

-- [39] MultiElementGroup ::= UnaryTripleExpr (';' UnaryTripleExpr)+ ';'?
  define "MultiElementGroup" [
    list["UnaryTripleExpr", plus(list[semicolon_, "UnaryTripleExpr"]), opt(semicolon_)]],

-- [40] UnaryTripleExpr ::= ('$' TripleExprLabel)? (TripleConstraint | BracketedTripleExpr) | Include
  define "UnaryTripleExpr" [
    list[opt(list[dollar_, "TripleExprLabel"]), alts["TripleConstraint", "BracketedTripleExpr"]],
    "Include"],

-- [41] BracketedTripleExpr ::= '(' InnerTripleExpr ')' Cardinality? Annotation* SemanticActions
  define "BracketedTripleExpr" [
    list[parenOpen_, "InnerTripleExpr", parenClose_, opt"Cardinality", star"Annotation", "SemanticActions"]],

-- [43] TripleConstraint ::= SenseFlags? Predicate InlineShapeExpression Cardinality? Annotation* SemanticActions
  define "TripleConstraint" [
    list[opt"SenseFlags", "Predicate", "InlineShapeExpression", opt"Cardinality", star"Annotation", "SemanticActions"]],

-- [44] Cardinality ::= '*' | '+' | '?' | RepeatRange
  define "Cardinality" [
    star_, plus_, question_, "RepeatRange"],


-- [45] SenseFlags ::= '^'
  define "SenseFlags" [
    terminal "^"],

-- [46] ValueSet ::= '[' ValueSetValue* ']'
  define "ValueSet" [
    list[terminal "[", star"ValueSetValue", terminal "]"]],

-- [47] ValueSetValue ::= IriRange | Literal
  define "ValueSetValue" [
    "IriRange",
    "Literal"],

-- [48] IriRange ::= Iri ('~' Exclusion*)? | '.' Exclusion+
  define "IriRange" [
    list["Iri", opt(list[tilde_, star"Exclusion"])],
    list[period_, plus"Exclusion"]],

-- [49] Exclusion ::= '-' Iri '~'?
  define "Exclusion" [
    list[dash_, "Iri", tilde_]],

-- [50] Include ::= '&' TripleExprLabel
  define "Include" [
    list[ampersand_, "TripleExprLabel"]],

-- [51] Annotation ::= '//' Predicate (Iri | Literal)
  define "Annotation" [
    list[terminal "//", "Predicate", alts["Iri", "Literal"]]],

-- [52] SemanticActions ::= CodeDecl*
  define "SemanticActions" [
    star"CodeDecl"],

-- [53] CodeDecl ::= '%' Iri (Code | "%")
  define "CodeDecl" [
    list[percent_, "Iri", alts["Code", percent_]]],

-- [13t] Literal ::= RdfLiteral | NumericLiteral | BooleanLiteral
  define "Literal" [
    "RdfLiteral",
    "NumericLiteral",
    "BooleanLiteral"],

-- [54] Predicate ::= Iri | RdfType
  define "Predicate" [
    "Iri",
    "RdfType"],

-- [55] Datatype ::= Iri
  define "Datatype" [
    "Iri"],

-- [56] ShapeExprLabel ::= Iri | BlankNode
  define "ShapeExprLabel" [
    "Iri",
    "BlankNode"],

-- [42] TripleExprLabel ::= '$' (Iri | BlankNode)
  define "TripleExprLabel" [
    list[dollar_, alts["Iri", "BlankNode"]]],

-- [16t] NumericLiteral ::= Integer | Decimal | Double
  define "NumericLiteral" [
    "Integer", "Decimal", "Double"],

-- [129s] RdfLiteral ::= String (LangTag | '^^' Datatype)?
  define "RdfLiteral" [
    list["String", opt(alts["LangTag", list[terminal "^^", "Datatype"]])]],

-- [134s] BooleanLiteral ::= 'true' | 'false'
  define "BooleanLiteral" [
    true_, false_],

-- [135s] String ::= StringLiteral1 | StringLiteralLong1
--                 | StringLiteral2 | StringLiteralLong2
  define "String" [
    "StringLiteral1",
    "StringLiteralLong1",
    "StringLiteral2",
    "StringLiteralLong2"],

-- [136s] Iri ::= IriRef | PrefixedName
  define "Iri" [
    "IriRef",
    "PrefixedName"],

-- [137s] PrefixedName ::= PnameLn | PnameNs
  define "PrefixedName" [
    "PnameLn",
    "PnameNs"],

-- [138s] BlankNode ::= BlankNodeLabel
  define "BlankNode" [
    "BlankNodeLabel"],

--   # Reserved for future use
-- [57] IncludeSet ::= '&' ShapeExprLabel+
  define "IncludeSet" [
    list[ampersand_, plus"ShapeExprLabel"]],

-- [58] Code ::= '{' ([^%\\] | '\\' [%\\] | Uchar)* '%' '}'
  define "Code" [
    list[braceOpen_, star(alts[ regex "[^%\\]", list[doubleFrwSlash_, regex "[%\\]"], "Uchar" ]), percent_, braceClose_]],

-- [59] RepeatRange ::= '{' Integer (',' (Integer | '*')?)? '}'
  define "RepeatRange" [
    list[braceOpen_, "Integer", opt(list[coma_, opt(opt(alts["Integer", star_]))]), braceClose_]],

-- [60] RdfType ::= 'a'
  define "RdfType" [
    terminal "a"],

-- [18t] IriRef ::= '<' ([^#x00-#x20<>\"{}|^`\\] | Uchar)* '>' /* #x00=NULL #01-#x1F=control codes #x20=space */
  define "IriRef" [
    list[terminal "<", star(alts[ regex "[^#x00-#x20<>\"{}|^`\\]", "Uchar"]), terminal ">"]],

-- [140s] PnameNs ::= PnPrefix? ':'
  define "PnameNs" [
    list[opt"PnPrefix", semicolon_]],

-- [141s] PnameLn ::= PnameNs PnLocal
  define "PnameLn" [
    list["PnameNs", "PnLocal"]],

-- [61] AtpNameNs ::= '@' PnPrefix? ':'
  define "AtpNameNs" [
    list[at_, opt"PnPrefix", colon_]],

-- [62] AtpNameLn ::= '@' PnameNs PnLocal
  define "AtpNameLn" [
    list[at_, "PnameNs", "PnLocal"]],

-- [63] Regexp ::= '~/' ([^#x2f#x5C#xA#xD] | '\\' [tbnrf\\/] | Uchar)* '/' [smix]*
  define "Regexp" [
    list[terminal "~/", star(alts[
        regex "[^#x2f#x5C#xA#xD]",
        list[terminal "\\", regex "[tbnrf\\/]"], "Uchar"]),
        terminal "/", star( regex "[smix]")
    ]],

-- [142s] BlankNodeLabel ::= '_:' (PnCharsU | [0-9]) ((PnChars | '.')* PnChars)?
  define "BlankNodeLabel" [
    list[terminal "_:", alts["PnCharsU", regex "[0-9]"], opt(star(alts["PnChars", period_])),"PnChars"]],

-- [145s] LangTag ::= '@' [a-zA-Z]+ ('-' [a-zA-Z0-9]+)*
  define "LangTag" [
    regex "@[a-zA-Z]+('-'[a-zA-Z0-9]+)*"],

-- [19t] Integer ::= [+-]? [0-9]+
  define "Integer" [
    regex "[+-]? [0-9]+"],

-- [20t] Decimal ::= [+-]? [0-9]* '.' [0-9]+
  define "Decimal" [
    regex "[+-]? [0-9]*\\.[0-9]+"],

-- [21t] Double ::= [+-]? ([0-9]+ '.' [0-9]* EXPONENT | '.'? [0-9]+ EXPONENT)
-- [155s] EXPONENT ::= [eE] [+-]? [0-9]+
  define "Double" [
    regex "([+-]?([0-9]+)?\\.[0-9]*[eE][+-]?[0-9]+"],

-- [156s] StringLiteral1 ::= "'" ([^#x27#x5C#xA#xD] | Echar | Uchar)* "'" /* #x27=' #x5C=\ #xA=new line #xD=carriage return */
  define "StringLiteral1" [
    list[singleQuote_, star(alts[regex "[^#x27#x5C#xA#xD]", "Echar", "Uchar"]), singleQuote_]],

-- [157s] StringLiteral2 ::= '"' ([^#x22#x5C#xA#xD] | Echar | Uchar)* '"' /* #x22=" #x5C=\ #xA=new line #xD=carriage return */
  define "StringLiteral2" [
    list[doubleQuote_, star(alts[regex "[^#x22#x5C#xA#xD]", "Echar", "Uchar"]), doubleQuote_]],

-- [158s] StringLiteralLong1 ::= "'''" (("'" | "''")? ([^\'\\] | Echar | Uchar))* "'''"
  define "StringLiteralLong1" [
    list[singleQuote_, singleQuote_, singleQuote_,
        star(alts[list[ opt(alts[singleQuote_, list[singleQuote_,singleQuote_]]), regex "[^\'\\]"], "Echar", "Uchar"]),
        singleQuote_, singleQuote_, singleQuote_]],

-- [159s] StringLiteralLong2 ::= '"""' (('"' | '""')? ([^\"\\] | Echar | Uchar))* '"""'
  define "StringLiteralLong2" [
    list[doubleQuote_, doubleQuote_, doubleQuote_,
        star(alts[list[ opt(alts[doubleQuote_, list[doubleQuote_,doubleQuote_]]), regex "[^\"\\]"], "Echar", "Uchar"]),
        doubleQuote_, doubleQuote_, doubleQuote_]],

-- [26t] Uchar ::= '\\u' Hex Hex Hex Hex
--                                   | '\\U' Hex Hex Hex Hex Hex Hex Hex Hex
  define "Uchar" [
    list[terminal "\\u", "Hex", "Hex", "Hex", "Hex"],
    list[terminal "\\U", "Hex", "Hex", "Hex", "Hex", "Hex", "Hex", "Hex", "Hex"]],

-- [160s] Echar ::= '\\' [tbnrf\\\"\']
  define "Echar" [
    list[doubleFrwSlash_, regex "[tbnrf\\\"\']"]],

-- [164s] PnCharsBase ::= [A-Z] | [a-z]
--                                   | [#x00C0-#x00D6] | [#x00D8-#x00F6] | [#x00F8-#x02FF]
--                                   | [#x0370-#x037D] | [#x037F-#x1FFF]
--                                   | [#x200C-#x200D] | [#x2070-#x218F] | [#x2C00-#x2FEF]
--                                   | [#x3001-#xD7FF] | [#xF900-#xFDCF] | [#xFDF0-#xFFFD]
--                                   | [#x10000-#xEFFFF]
  define "PnCharsBase" [
    regex "[A-Z]",
    regex "[a-z]"], -- TODO other chars


-- [165s] PnCharsU ::= PnCharsBase | '_'
  define "PnCharsU" [
    "PnCharsBase",
    underscore_],

-- [167s] PnChars ::= PnCharsU | '-' | [0-9]
--                                   | [#x00B7] | [#x0300-#x036F] | [#x203F-#x2040]
  define "PnChars" [
    "PnCharsU",
    dash_,
    regex "0-9"], -- TODO other chars

-- [168s] PnPrefix ::= PnCharsBase ((PnChars | '.')* PnChars)?
  define "PnPrefix" [
    list["PnCharsBase",
    opt(list[alts["PnChars", period_],"PnChars"])]],

-- [169s] PnLocal ::= (PnCharsU | ':' | [0-9] | Plx) ((PnChars | '.' | ':' | Plx)* (PnChars | ':' | Plx))?
  define "PnLocal" [
    list[
      alts["PnCharsU", colon_, regex "0-9", "Plx"],
      opt(list[
        star(alts["PnChars", period_, colon_, "Plx"]),
        alts["PnChars", colon_, "Plx"]]
      )]],

-- [170s] Plx ::= Percent | PnLocalEsc
  define "Plx" [
    "Percent",
    "PnLocalEsc"],

-- [171s] Percent ::= '%' Hex Hex
  define "Percent" [
    list[percent_, "Hex", "Hex"]],

-- [172s] Hex ::= [0-9] | [A-F] | [a-f]
  define "Hex" [regex "[0-9][A-F][a-f]"],


-- [173s] PnLocalEsc ::= '\\' ('_' | '~' | '.' | '-' | '!' | '$' | '&' | "'" | '(' | ')' | '*' | '+' | ',' | ';' | '=' | '/' | '?' | '#' | '@' | '%')
  define "PnLocalEsc" [
    list[doubleFrwSlash_, regex "[_~\\.-!$&'\\(\\)\\*+,;=/\\?#@%]"]]]

--   @pass ::= [ \t\r\n]+ -- TODO
--           | "#" [^\r\n]*

