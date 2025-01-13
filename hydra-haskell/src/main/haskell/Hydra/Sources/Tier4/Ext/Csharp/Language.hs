{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Ext.Csharp.Language where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Base as Base
import Hydra.Dsl.Coders as Coders
import Hydra.Dsl.Lib.Equality as Equality
import Hydra.Dsl.Lib.Flows as Flows
import Hydra.Dsl.Lib.Lists as Lists
import Hydra.Dsl.Lib.Logic as Logic
import Hydra.Dsl.Lib.Maps as Maps
import Hydra.Dsl.Lib.Sets as Sets
import Hydra.Dsl.Lib.Strings as Strings
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Data.Set as S


csharpLanguageDefinition :: String -> TTerm a -> TElement a
csharpLanguageDefinition = definitionInModule csharpLanguageModule

csharpLanguageModule :: Module
csharpLanguageModule = Module ns elements [hydraCodersModule, hydraBasicsModule] tier0Modules $
    Just "Language constraints and reserved words for C Sharp (C#)"
  where
    ns = Namespace "hydra/ext/csharp/language"
    elements = [
      el csharpLanguageDef,
      el csharpReservedWordsDef]

csharpLanguageDef :: TElement Language
csharpLanguageDef = csharpLanguageDefinition "csharpLanguage" $
    doc "Language constraints for C Sharp (C#)" $
    typed languageT $
    Coders.language "hydra/ext/csharp"
      eliminationVariants
      literalVariants
      floatTypes
      functionVariants
      integerTypes
      termVariants
      typeVariants
      typePredicate
  where
      eliminationVariants = [ -- TODO: verify whether all are supported
        EliminationVariantList,
        EliminationVariantOptional,
        EliminationVariantProduct,
        EliminationVariantRecord,
        EliminationVariantUnion,
        EliminationVariantWrap]
      literalVariants = [
        LiteralVariantBinary, -- byte[]
        LiteralVariantBoolean, -- bool
        LiteralVariantFloat, -- (see float types)
        LiteralVariantInteger, -- (see integer types)
        LiteralVariantString] -- String/string
      -- See: https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/builtin-types/floating-point-numeric-types
      -- Note: the other C# floating point type, decimal, has no equivalent in Hydra
      floatTypes = [
        FloatTypeFloat32,
        FloatTypeFloat64]
      functionVariants = [
        FunctionVariantElimination,
        FunctionVariantLambda,
        FunctionVariantPrimitive]
      -- See https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/builtin-types/integral-numeric-types
      -- Note: the other two C# integral types, nint and nuint, have no equivalents in Hydra
      integerTypes = [
        IntegerTypeInt8, -- sbyte
        IntegerTypeInt16, -- short
        IntegerTypeInt32, -- int
        IntegerTypeInt64, -- long
        IntegerTypeUint8, -- byte
        IntegerTypeUint16, -- ushort
        IntegerTypeUint32, -- uint
        IntegerTypeUint64] -- ulong
      termVariants = [ -- TODO: verify whether all are supported
        TermVariantApplication,
        TermVariantFunction,
        TermVariantLet,
        TermVariantList,
        TermVariantLiteral,
        TermVariantMap,
        TermVariantOptional,
        TermVariantProduct,
        TermVariantRecord,
        TermVariantSet,
        TermVariantUnion,
        TermVariantVariable,
        TermVariantWrap]
      typeVariants = [ -- TODO: verify whether all are supported
        TypeVariantAnnotated,
        TypeVariantApplication,
        TypeVariantFunction,
        TypeVariantLambda,
        TypeVariantList,
        TypeVariantLiteral,
        TypeVariantMap,
        TypeVariantOptional,
        TypeVariantProduct,
        TypeVariantRecord,
        TypeVariantSet,
        TypeVariantUnion,
        TypeVariantVariable,
        TypeVariantWrap]
      typePredicate = constant true -- TODO: verify whether all are supported

csharpReservedWordsDef :: TElement (S.Set String)
csharpReservedWordsDef = csharpLanguageDefinition "csharpReservedWords" $
    doc ("A set of reserved words in C#. Both the \"keywords\" and \"contextual keywords\" are drawn from"
      <> " section 6.4.4 of the C# documentation:\n"
      <> "https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/language-specification/lexical-structure#64-tokens") $
    typed (setT stringT) $
    (Sets.fromList @@ (Lists.concat @@ list [var "keywords", var "contextualKeywords"]))
  `with` [
    "keywords">: list [
        "DEFAULT", "FALSE", "NULL", "TRUE",
        "abstract", "as", "base", "bool", "break", "byte", "case", "catch", "char", "checked", "class", "const",
        "continue", "decimal", "delegate", "do", "double", "else", "enum", "event", "explicit", "extern", "finally",
        "fixed", "float", "for", "foreach", "goto", "if", "implicit", "in", "int", "interface", "internal", "is",
        "lock", "long", "namespace", "new", "object", "operator", "out", "override", "params", "private", "protected",
        "public", "readonly", "ref", "return", "sbyte", "sealed", "short", "sizeof", "stackalloc", "static", "string",
        "struct", "switch", "this", "throw", "try", "typeof", "uint", "ulong", "unchecked", "unsafe", "ushort", "using",
        "virtual", "void", "volatile", "while"],
    "contextualKeywords">: list [
        "add", "alias", "ascending", "async", "await", "by", "descending", "dynamic", "equals", "from", "get", "global",
        "group", "into", "join", "let", "nameof", "on", "orderby", "partial", "remove", "select", "set", "unmanaged",
        "value", "var", "when", "where", "yield"]]