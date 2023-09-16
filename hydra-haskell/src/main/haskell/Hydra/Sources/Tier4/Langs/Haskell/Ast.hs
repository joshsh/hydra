module Hydra.Sources.Tier4.Langs.Haskell.Ast where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types


haskellAstModule :: Module
haskellAstModule = Module ns elements [hydraCoreModule] $
    Just "A Haskell syntax model, loosely based on Language.Haskell.Tools.AST"
  where
    ns = Namespace "hydra/langs/haskell/ast"
    def = datatype ns
    ast = typeref ns

    elements = [

      def "Alternative" $ -- UAlt
        doc "A pattern-matching alternative" $
        record [
          "pattern">: ast "Pattern",
          "rhs">: ast "CaseRhs",
          "binds">: optional $ ast "LocalBindings"],

      def "Assertion" $ -- UAssertion (UClassAssert)
        doc "A type assertion" $
        union [
          "class">: ast "Assertion.Class",
          "tuple">: list $ ast "Assertion"],
        -- omitted for now: implicit and infix assertions

      def "Assertion.Class" $ -- UClassAssert
        record [
          "name">: ast "Name",
          "types">: list $ ast "Type"],

      def "CaseRhs" $ -- UCaseRhs'
        doc "The right-hand side of a pattern-matching alternative" $
        -- omitted for now: guarded
        ast "Expression",

      def "Constructor" $ -- UConDecl
        doc "A data constructor" $
        -- omitted for now: ordinary (positional), infix
        union [
          "ordinary">: ast "Constructor.Ordinary",
          "record">: ast "Constructor.Record"],

      def "Constructor.Ordinary" $
        doc "An ordinary (positional) data constructor" $
        record [
          "name">: ast "Name",
          "fields">: list $ ast "Type"],

      def "Constructor.Record" $
        doc "A record-style data constructor" $
        record [
          "name">: ast "Name",
          "fields">: list $ ast "FieldWithComments"],

      def "ConstructorWithComments" $
        doc "A data constructor together with any comments" $
        record [
          "body">: ast "Constructor",
          "comments">: optional string],

      def "DataDeclaration" $ -- UDataDecl
        doc "A data type declaration" $
        record [
          "keyword">: ast "DataDeclaration.Keyword",
          "context">: list $ ast "Assertion",
          "head">: ast "DeclarationHead",
          "constructors">: list $ ast "ConstructorWithComments",
          "deriving">: list $ ast "Deriving"],

      def "DataDeclaration.Keyword" $
        doc "The 'data' versus 'newtype keyword" $
        enum ["data", "newtype"],

      def "DeclarationWithComments" $
        doc "A data declaration together with any comments" $
        record [
          "body">: ast "Declaration",
          "comments">: optional string],

      def "Declaration" $ -- UDecl
        doc "A data or value declaration" $
        -- omitted for now: typeFamily, typeSignature, closedTypeFamily, gDataDecl, typeInst, dataInst, gDataInst, class, inst,
        --                  patternSynonym, deriv, fixity, default, patTypeSig, foreignImport, foreignExport, pragma,
        --                  role, splice
        union [
          "data">: ast "DataDeclaration",
          "type">: ast "TypeDeclaration",
          "valueBinding">: ast "ValueBinding",
          "typedBinding">: ast "TypedBinding"],

      def "DeclarationHead" $ -- UDeclHead
        doc "The left-hand side of a declaration" $
        -- omitted for now: infix application
        union [
          "application">: ast "DeclarationHead.Application",
          "parens">: ast "DeclarationHead",
          "simple">: ast "Name"],

      def "DeclarationHead.Application" $
        doc "An application-style declaration head" $
        record [
          "function">: ast "DeclarationHead",
          "operand">: ast "Variable"],

      def "Deriving" $ -- UDeriving
        doc "A 'deriving' statement" $
        -- omitted for now: infix, parenthesized, and application instance heads
        list $ ast "Name",

      def "Export" $ -- UExportSpec
        doc "An export statement" $
        union [
          "declaration">: ast "ImportExportSpec",
          "module">: ast "ModuleName"],

      def "Expression" $ -- UExpr
        doc "A data expression" $
        -- omitted for now: multi-if, unboxed tuple, tuple section, unboxed tuple section, parallel array,
        --                  enum, parallel array enum, list comp, parallel array comp, type application,
        --                  (all Template Haskell constructors), pragma, arrow definition, arrow application,
        --                  lambda cases, static, unboxed sum, hole
        union [
          "application">: ast "Expression.Application",
          "case">: ast "Expression.Case",
          "constructRecord">: ast "Expression.ConstructRecord",
          "do">: list $ ast "Statement", -- omitted for now: do vs. mdo
          "if">: ast "Expression.If",
          "infixApplication">: ast "Expression.InfixApplication",
          "literal">: ast "Literal",
          "lambda">: ast "Expression.Lambda",
          "leftSection">: ast "Expression.Section",
          "let">: ast "Expression.Let",
          "list">: list $ ast "Expression",
          "parens">: ast "Expression",
          "prefixApplication">: ast "Expression.PrefixApplication",
          "rightSection">: ast "Expression.Section",
          "tuple">: list $ ast "Expression",
          "typeSignature">: ast "Expression.TypeSignature",
          "updateRecord">: ast "Expression.UpdateRecord",
          "variable">: ast "Name"],

      def "Expression.Application" $
        doc "An application expression" $
        record [
          "function">: ast "Expression",
          "argument">: ast "Expression"],

      def "Expression.Case" $
        doc "A case expression" $
        record [
          "case">: ast "Expression",
          "alternatives">: list $ ast "Alternative"],

      def "Expression.ConstructRecord" $
        doc "A record constructor expression" $
        record [
          "name">: ast "Name",
          "fields">: list $ ast "FieldUpdate"],

      def "Expression.If" $
        doc "An 'if' expression" $
        record [
          "condition">: ast "Expression",
          "then">: ast "Expression",
          "else">: ast "Expression"],

      def "Expression.InfixApplication" $
        doc "An infix application expression" $
        record [
          "lhs">: ast "Expression",
          "operator">: ast "Operator",
          "rhs">: ast "Expression"],

      def "Expression.Lambda" $
        doc "A lambda expression" $
        record [
          "bindings">: list $ ast "Pattern",
          "inner">: ast "Expression"],

      def "Expression.Let" $
        doc "A 'let' expression" $
        record [
          "bindings">: list $ ast "LocalBinding",
          "inner">: ast "Expression"],

      def "Expression.PrefixApplication" $
        doc "A prefix expression" $
        record [
          "operator">: ast "Operator",
          "rhs">: ast "Expression"],

      def "Expression.Section" $
        doc "A section expression" $
        record [
          "operator">: ast "Operator",
          "expression">: ast "Expression"],

      def "Expression.TypeSignature" $
        doc "A type signature expression" $
        record [
          "inner">: ast "Expression",
          "type">: ast "Type"],

      def "Expression.UpdateRecord" $
        doc "An update record expression" $
        record [
          "inner">: ast "Expression",
          "fields">: list $ ast "FieldUpdate"],

      def "Field" $ -- UFieldDecl
        doc "A field (name/type pair)" $
        record [
          "name">: ast "Name",
          "type">: ast "Type"],

      def "FieldWithComments" $
        doc "A field together with any comments" $
        record [
          "field">: ast "Field",
          "comments">: optional string],

      def "FieldUpdate" $ -- UFieldUpdate
        doc "A field name and value" $
        -- omitted for now: pun, wildcard
        record [
          "name">: ast "Name",
          "value">: ast "Expression"],

      def "Import" $ -- UImportDecl
        doc "An import statement" $
        -- omitted for now: source, safe, pkg
        record [
          "qualified">: boolean,
          "module">: ast "ModuleName",
          "as">: optional $ ast "ModuleName",
          "spec">: optional $ ast "Import.Spec"],

      def "Import.Spec" $
        doc "An import specification" $
        union [
          "list">: list $ ast "ImportExportSpec",
          "hiding">: list $ ast "ImportExportSpec"],

      def "ImportModifier" $ -- UImportModifier
        doc "An import modifier ('pattern' or 'type')" $
        enum ["pattern", "type"],

      def "ImportExportSpec" $ -- UIESpec
        doc "An import or export specification" $
        record [
          "modifier">: optional $ ast "ImportModifier",
          "name">: ast "Name",
          "subspec">: optional $ ast "ImportExportSpec.Subspec"],

      def "ImportExportSpec.Subspec" $
        union [
          "all">: unit,
          "list">: list $ ast "Name"],

      def "Literal" $ -- ULiteral
        doc "A literal value" $
        -- omitted for now: frac, primChar
        union [
          "char">: uint16,
          "double">: float64,
          "float">: float32,
          "int">: int32,
          "integer">: bigint,
          "string">: string],

      def "LocalBinding" $ -- ULocalBind
        -- omitted for now: fixity, pragma
        union [
          "signature">: ast "TypeSignature",
          "value">: ast "ValueBinding"],

      def "LocalBindings" $ -- ULocalBinds
        list $ ast "LocalBinding",

      def "Module" $ -- UModule
        -- omitted for now: pragma
        record [
          "head">: optional $ ast "ModuleHead",
          "imports">: list $ ast "Import",
          "declarations">: list $ ast "DeclarationWithComments"],

      def "ModuleHead" $ -- UModuleHead
        -- omitted for now: pragma
        record [
          "comments">: optional string,
          "name">: ast "ModuleName",
          "exports">: list $ ast "Export"], -- UExportSpecs

      def "ModuleName" -- UModuleName
        string,

      def "Name" $ -- UName
        union [
          "implicit">: ast "QualifiedName",
          "normal">: ast "QualifiedName",
          "parens">: ast "QualifiedName"],

      def "NamePart" -- UNamePart
        string,

      def "Operator" $ -- UOperator
        union [
          "backtick">: ast "QualifiedName",
          "normal">: ast "QualifiedName"],

      def "Pattern" $ -- UPattern
        -- omitted for now: unboxed tuples, parallel arrays, irrefutable, bang, view, splice, quasiquote, plusk, unboxed sum
        union [
          "application">: ast "Pattern.Application",
          "as">: ast "Pattern.As",
          "list">: list $ ast "Pattern",
          "literal">: ast "Literal",
          "name">: ast "Name",
          "parens">: ast "Pattern",
          "record">: ast "Pattern.Record",
          "tuple">: list $ ast "Pattern",
          "typed">: ast "Pattern.Typed",
          "wildcard">: unit],

      def "Pattern.Application" $
        record [
          "name">: ast "Name",
          "args">: list $ ast "Pattern"],

      def "Pattern.As" $
        record [
          "name">: ast "Name",
          "inner">: ast "Pattern"],

      def "Pattern.Record" $
        record [
          "name">: ast "Name",
          "fields">: list $ ast "PatternField"],

      def "Pattern.Typed" $
        record [
          "inner">: ast "Pattern",
          "type">: ast "Type"],

      def "PatternField" $ -- UPatternField
        -- omitted for now: puns, wildcards
        record [
          "name">: ast "Name",
          "pattern">: ast "Pattern"],

      def "QualifiedName" $ -- UQualifiedName
        record [
          "qualifiers">: list $ ast "NamePart",
          "unqualified">: ast "NamePart"],

      def "RightHandSide" $ -- URhs
        -- omitted for now: guarded rhs
        ast "Expression",

      def "Statement" $ -- UStmt
        ast "Expression",

      def "Type" $ -- UType
        -- omitted for now: forall, unboxed tuple, parallel array, kinded, promoted, splice, quasiquote, bang,
        --                  lazy, unpack, nounpack, wildcard, named wildcard, sum
        union [
          "application">: ast "Type.Application",
          "ctx">: ast "Type.Context",
          "function">: ast "Type.Function",
          "infix">: ast "Type.Infix",
          "list">: ast "Type",
          "parens">: ast "Type",
          "tuple">: list $ ast "Type",
          "variable">: ast "Name"],

      def "Type.Application" $
        record [
          "context">: ast "Type",
          "argument">: ast "Type"],

      def "Type.Context" $
        record [
          "ctx">: ast "Assertion", -- UContext
          "type">: ast "Type"],

      def "Type.Function" $
        record [
          "domain">: ast "Type",
          "codomain">: ast "Type"],

      def "Type.Infix" $
        record [
          "lhs">: ast "Type",
          "operator">: ast "Operator",
          "rhs">: ast "Operator"],

      def "TypeDeclaration" $ -- UTypeDecl
        record [
          "name">: ast "DeclarationHead",
          "type">: ast "Type"],

      def "TypeSignature" $ -- UTypeSignature
        record [
          "name">: ast "Name",
          "type">: ast "Type"],

      def "TypedBinding" $ -- Added for convenience
        record [
          "typeSignature">: ast "TypeSignature",
          "valueBinding">: ast "ValueBinding"],

      def "ValueBinding" $ -- UValueBind
        -- omitted for now: funBind
        union [
          "simple">: ast "ValueBinding.Simple"],

      def "ValueBinding.Simple" $
        record [
          "pattern">: ast "Pattern",
          "rhs">: ast "RightHandSide",
          "localBindings">: optional $ ast "LocalBindings"],

      def "Variable" $
        -- omitted for now: kind constraints
        ast "Name"]
