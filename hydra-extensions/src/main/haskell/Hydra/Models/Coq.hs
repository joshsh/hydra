module Hydra.Models.Coq where

import Hydra.Dsl.Types as Types
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Annotations
import Hydra.Sources.Tier4.All


coqSyntaxModule :: Module
coqSyntaxModule = Module ns elements [] $
    Just ("A model for Coq core and extensions. Based on the Coq 8.15 grammar:\n" ++
      "  https://coq.github.io/doc/v8.15/refman/language/core/basic.html#essential-vocabulary")
  where
    ns = Namespace "hydra/langs/coq/syntax"
    def = datatype ns
    coq = typeref ns

    elements = [

      def "AnnotatedApplication" $ record [
        "annot">: coq "QualidAnnotated",
        "terms">: nonemptyList $ coq "Term1"],

      def "Application" $ union [
        "normal">: coq "NormalApplication",
        "annotated">: coq "AnnotatedApplication"],

      def "Arg" $ union [
        "ident">: coq "IdentArg",
        "natural">: coq "NaturalArg",
        "term">: coq "Term1"],

      def "Binder" $ union [
        "name">: coq "Name",
        "type">: coq "TypeBinders",
        "term">: coq "LetBinder",
        "implicit">: coq "ImplicitBinders",
        "generalizing">: coq "GeneralizingBinder",
        -- 	( name : type | term )  -- TODO
        "pattern">: coq "Pattern0"],

      def "CaseItem" $ record [
        "term">: coq "Term100",
        "as">: optional $ coq "Name",
        "in">: optional $ coq "Pattern"],

      def "Cofix" $ record [
        "body">: coq "CofixBody",
        "qual">: optional $ coq "CofixQual"],

      def "CofixBody" $ record [
        "ident">: coq "Ident",
        "binders">: list $ coq "Binder",
        "type">: optional $ coq "Type",
        "term">: coq "Term"],

      def "CofixQual" $ union [
        "in">: coq "Term",
        "with">: coq "CofixWith"],

      def "CofixWith" $ record [
        "with">: nonemptyList $ coq "CofixBody",
        "for">: optional $ coq "Ident"],

      def "Equation" $ record [
        "pattern">: nonemptyList $ nonemptyList $ coq "Pattern",
        "term">: coq "Term"],

      def "ExistentialVariable" $ record [
        "ident">: coq "Ident",
        "variant">: coq "ExistentialVariableVariant"],

      def "ExistentialVariableVariant" $ union [
        "placeholder">: unit,
        "inside1">: unit,
        "inside2">: unit,
        "outside">: optional $ coq "IdentArg"],

      def "FieldIdent" $ coq "Ident",

      def "Fix" $ union [
        "decl">: coq "Fix.Decl",
        "qual">: optional $ coq "Fix.Qual"],

      def "FixAnnot" $ union [
        "struct">: coq "Ident",
        "wf">: coq "FixAnnot.Wf",
        "measure">: coq "FixAnnot.Measure"],

      def "FixAnnot.Measure" $ record [
        "term">: coq "OneTerm",
        "ident">: optional $ coq "Ident",
        "term2">: optional $ coq "OneTerm"],

      def "FixAnnot.Wf" $ record [
        "term">: coq "OneTerm",
        "ident">: coq "Ident"],

      def "Fix.Decl" $ record [
        "ident">: coq "Ident",
        "binders">: list $ coq "Binder",
        "annot">: optional $ coq "FixAnnot",
        "type">: optional $ coq "Type",
        "term">: coq "Term"],

      def "Fix.Qual" $ union [
        "in">: coq "Term",
        "with">: coq "FixWith"],

      def "FixWith" $ record [
        "decls">: nonemptyList $ coq "Fix.Decl",
        "for">: optional $ coq "Ident"],

      def "Forall" $ record [
        "binders">: coq "OpenBinders",
        "type">: coq "Type"],

      def "ForallOrFun" $ union [
        "forall">: coq "Forall",
        "fun">: coq "Fun"],

      def "Fun" $ record [
        "binders">: coq "OpenBinders",
        "body">: coq "Term"],

      def "GeneralizingBinder" $ union [
        "explicit">:
          doc "Terms surrounded by `( ) introduce their free variables as explicit arguments" $
          coq "TypeclassConstraint",

        "implicitMaximallyInserted">:
          doc "Terms surrounded by `{ } introduce their free variables as maximally inserted implicit arguments" $
          coq "TypeclassConstraint",

        "implicitNonMaximallyInserted">:
          doc "Terms surrounded by `[ ] introduce them as non-maximally inserted implicit arguments" $
          coq "TypeclassConstraint"],

      def "Ident" $ coq "String",

      def "IdentArg" $ record [
        "ident">: coq "Ident",
        "term">: coq "Term"],

      def "If" $
        doc "Pattern match on boolean values" $
        record [
          "condition">: coq "Term",
          "returnAs">: optional $ coq "ReturnAs",
          "then">: coq "Term",
          "else">: coq "Term"],

      def "ImplicitBinders" $
        doc "In the context of a function definition, these forms specify that name is an implicit argument." $
        union [
          "maximallyInserted">:
            doc "The first form, with curly braces, makes name a maximally inserted implicit argument" $
            coq "TypeBinders",

          "nonMaximallyInserted">:
            doc "The second form, with square brackets, makes name a non-maximally inserted implicit argument." $
            coq "TypeBinders"],

      def "Let" $
        doc "A let-in definition" $
        record [
          "bindings">: coq "LetBindings",
          "in">: coq "Term"],

      def "LetBinder" $
        doc "Some constructions allow the binding of a variable to value. This is called a “let-binder”." $
        record [
          "name">: coq "Name",
          "type">: optional $ coq "Type",
          "term">: coq "Term"],

      def "LetBindings" $ union [
        "named">: coq "LetNamed",
        "destructuring">: coq "LetDestructuring"],

      def "LetNamed" $ record [
        "binder">: coq "LetBinder",
        "binders">: list $ coq "Binder"],

      def "LetDestructuring" $ union [
        "variant1">: coq "LetDestructuring.Variant1",
        "variant2">: coq "LetDestructuring.Variant2",
        "variant3">: coq "LetDestructuring.Variant3"],

      def "LetDestructuring.Variant1" $ record [
        "names">: list $ coq "Name",
        "returnAs">: optional $ coq "ReturnAs",
        "term">: coq "Term"],

      def "LetDestructuring.Variant2" $ record [
        "pattern">: coq "Pattern",
        "term">: coq "Term",
        "return">: optional $ coq "Term100"],

      def "LetDestructuring.Variant3" $ record [
        "pattern1">: coq "Pattern",
        "pattern2">: coq "Pattern",
        "term">: coq "Term",
        "return">: coq "Term100"],

      def "Match" $ record [
        "caseItems">: nonemptyList $ coq "CaseItem",
        "return">: optional $ coq "Term100",
        "pipe">: boolean,
        "equations">: list $ coq "Equation"],

      def "Name" $ optional $ coq "Ident",

      def "Natural" $
        doc "A non-negative arbitrary-precision integer"
        bigint,

      def "NaturalArg" $ record [
        "natural">: coq "Natural",
        "term">: coq "Term"],

      def "NormalApplication" $ record [
        "lhs">: coq "Term1",
        "rhs">: nonemptyList $ coq "Arg"],

      def "Number" bigfloat,

      def "OneTerm" $ union [
        "explicit">: coq "QualidAnnotated",
        "term1">: coq "Term1"],

      def "OpenBinders" $ union [
        "type">: coq "TypeBinders",
        "binders">: list $ coq "Binder"],

      def "Pattern" $ union [
        "pattern">: coq "Pattern10",
        "term">: optional $ coq "Term"],

      def "Pattern0" $ union [
        "qualid">: coq "Qualid",
        "qualIdAndPattern">: coq "QualidAndPattern",
        "placeholder">: unit,
        "parens">: nonemptyList $ coq "Pattern",
        "number">: coq "Number",
        "string">: coq "String"],

      def "Pattern1" $ record [
        "pattern">: coq "Pattern0",
        "scope">: optional $ coq "ScopeKey"],

      def "Pattern10" $ union [
        "as">: coq "Pattern10.As",
        "patterns">: coq "Pattern10.Patterns",
        "qualiid">: coq "Pattern10.Qualid"],

      def "Pattern10.As" $ record [
        "pattern">: coq "Pattern1",
        "as">: coq "Name"],

      def "Pattern10.Patterns" $ record [
        "pattern">: coq "Pattern1",
        "patterns">: list $ coq "Pattern1"],

      def "Pattern10.Qualid" $ record [
        "qualid">: coq "Qualid",
        "patterns">: list $ coq "Pattern1"],

      def "PrimitiveNotations" $ union [
        "number">: coq "Number",
        "string">: coq "String"],

      def "Qualid" $
        doc "A qualified identifier" $
        record [
          "id">: coq "Ident",
          "fieldIds">: list $ coq "FieldIdent"],

      def "QualidAndPattern" $ record [
        "qualid">: coq "Qualid",
        "pattern">: coq "Pattern"],

      def "QualidAnnotated" $ record [
        "qualid">: coq "Qualid",
        "univAnnot">: optional $ coq "UnivAnnot"],

      def "ReturnAs" $ record [
        "as">: optional $ coq "Name",
        "return">: coq "Term100"],

      def "ScopeKey" $ coq "Ident",

      def "Sort" $
        doc "The types of types are called sorts." $
        union [
          "set">:
            doc "The sort 𝖲𝖾𝗍 intends to be the type of small sets." unit,
          "prop">:
            doc "The sort 𝖯𝗋𝗈𝗉 intends to be the type of logical propositions." unit,
          "sProp">:
            doc "The sort 𝖲𝖯𝗋𝗈𝗉 is like 𝖯𝗋𝗈𝗉 but the propositions in 𝖲𝖯𝗋𝗈𝗉 are known to have irrelevant proofs (all proofs are equal)." unit,
          "type">: unit,
          "typeWithAnyUniverse">: unit,
          "typeWithUniverse">: coq "Universe"],

      def "String" string,

      def "Term" $ union [
        "forallOrFun">: coq "ForallOrFun",
        "let">: coq "Let",
        "if">: coq "If",
        "fix">: coq "Fix",
        "cofix">: coq "Cofix",
        "term100">: coq "Term100"],

      def "Term0" $ union [
        "qualidAnnotated">: coq "QualidAnnotated",
        "sort">: coq "Sort",
        "primitiveNotations">: coq "PrimitiveNotations",
        "evar">: coq "ExistentialVariable",
        "match">: coq "Match",
        "record">: unit,
        "generalizing">: unit,
        -- 	[| term*; | term : type? |] univ_annot? -- TODO
        "ltac">: unit,
        "parens">: coq "Term"],

      def "Term1" $ union [
        "projection">: unit,
        "scope">: unit,
        "term0">: coq "Term0"],

      def "Term10" $ union [
        "application">: coq "Application",
        "oneTerm">: coq "OneTerm"],

      def "Term100" $ union [
        "cast">: coq "TypeCast",
        "term10">: coq "Term10"],

      def "Type" $ coq "Term",

      def "TypeCast" $ record [
        "term">: coq "Term10",
        "type">: coq "Type",
        "operator">: coq "TypeCastOperator"],

      def "TypeCastOperator" $ union [
        "normal">:
          doc "The expression term10 : type is a type cast expression. It enforces the type of term10 to be type." unit,
        "vmCompute">:
          doc "term10 <: type specifies that the virtual machine will be used to type check that term10 has type type (see vm_compute)." unit,
        "nativeCompute">:
          doc "term10 <<: type specifies that compilation to OCaml will be used to type check that term10 has type type (see native_compute)." unit],

      def "TypeBinders" $ record [
        "names">: nonemptyList $ coq "Name",
        "type">: coq "Type"],

      def "TypeclassConstraint" $
        record [
          "name">: optional $ coq "Name",
          "generalizing">: boolean,
          "term">: coq "Term"],

      def "UnivAnnot" $ list $ coq "UniverseLevel",

      def "Universe" $ union [
        "max">: nonemptyList $ coq "Universe.Expr",
        "expr">: coq "Universe.Expr"],

      def "Universe.Expr" $ record [
        "name">: coq "UniverseName",
        "number">: optional $ coq "Natural"],

      def "UniverseLevel" $ union [
        "set">: unit,
        "prop">: unit,
        "type">: unit,
        "ignored">: unit,
        "qualid">: coq "Qualid"],

      def "UniverseName" $ union [
        "qualid">: coq "Qualid",
        "set">: unit,
        "prop">: unit]]
