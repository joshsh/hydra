module Hydra.Ext.Csharp.Serde where

import qualified Hydra.Ext.Csharp.Syntax as Cs
import Hydra.Tools.Serialization
import qualified Hydra.Ast as A

import qualified Data.List as L
import qualified Data.Maybe as Y


encodeAttributeSection :: Cs.AttributeSection -> A.Expr
encodeAttributeSection _ = unsupportedType "AttributeSection"

encodeClassBase :: Cs.ClassBase -> A.Expr
encodeClassBase _ = unsupportedType "ClassBase"

encodeClassBody :: Cs.ClassBody -> A.Expr
encodeClassBody _ = unsupportedType "ClassBody"

encodeClassDeclaration :: Cs.ClassDeclaration -> A.Expr
encodeClassDeclaration (Cs.ClassDeclaration attrs mods partial name params base constraints body) =
  spaceSep $ L.concat [
    (encodeAttributeSection <$> attrs),
    (encodeClassModifier <$> mods),
    (if partial then [cst "partial"] else []),
    [cst "class", encodeIdentifier name],
    (Y.maybe [] (\l -> [encodeTypeParameterList l]) params),
    (Y.maybe [] (\b -> [encodeClassBase b]) base),
    (encodeTypeParameterConstraintsClause <$> constraints),
    [encodeClassBody body]]

encodeClassModifier :: Cs.ClassModifier -> A.Expr
encodeClassModifier _ = unsupportedType "ClassModifier"

encodeCompilationUnit :: Cs.CompilationUnit -> A.Expr
encodeCompilationUnit (Cs.CompilationUnit externs usings attributes members) = doubleNewlineSep [
  newlineSep (encodeExternAliasDirective <$> externs),
  newlineSep (encodeUsingDirective <$> usings),
  newlineSep (encodeGlobalAttributeSection <$> attributes),
  newlineSep (encodeNamespaceMemberDeclaration <$> members)]

encodeDelegateDeclaration :: Cs.DelegateDeclaration -> A.Expr
encodeDelegateDeclaration _ = unsupportedType "DelegateDeclaration"

encodeEnumDeclaration :: Cs.EnumDeclaration -> A.Expr
encodeEnumDeclaration _ = unsupportedType "EnumDeclaration"

encodeExternAliasDirective :: Cs.ExternAliasDirective -> A.Expr
encodeExternAliasDirective _ = unsupportedType "ExternAliasDirective"

encodeGlobalAttributeSection :: Cs.GlobalAttributeSection -> A.Expr
encodeGlobalAttributeSection _ = unsupportedType "GlobalAttributeSection"

encodeIdentifier :: Cs.Identifier -> A.Expr
encodeIdentifier (Cs.Identifier s) = cst s

encodeInterfaceDeclaration :: Cs.InterfaceDeclaration -> A.Expr
encodeInterfaceDeclaration _ = unsupportedType "InterfaceDeclaration"

encodeNamespaceBody :: Cs.NamespaceBody -> A.Expr
encodeNamespaceBody (Cs.NamespaceBody externs usings members) = curlyBlock fullBlockStyle $ doubleNewlineSep [
  newlineSep (encodeExternAliasDirective <$> externs),
  newlineSep (encodeUsingDirective <$> usings),
  newlineSep (encodeNamespaceMemberDeclaration <$> members)]

encodeNamespaceDeclaration :: Cs.NamespaceDeclaration -> A.Expr
encodeNamespaceDeclaration (Cs.NamespaceDeclaration qi body) = withSemi $ spaceSep [
  cst "namespace",
  encodeQualifiedIdentifier qi,
  encodeNamespaceBody body]

encodeNamespaceMemberDeclaration :: Cs.NamespaceMemberDeclaration -> A.Expr
encodeNamespaceMemberDeclaration d = case d of
  Cs.NamespaceMemberDeclarationNamespace ns -> encodeNamespaceDeclaration ns
  Cs.NamespaceMemberDeclarationType t -> encodeTypeDeclaration t

encodeQualifiedIdentifier :: Cs.QualifiedIdentifier -> A.Expr
encodeQualifiedIdentifier (Cs.QualifiedIdentifier parts) = dotSep (encodeIdentifier <$> parts)

encodeStructDeclaration :: Cs.StructDeclaration -> A.Expr
encodeStructDeclaration _ = unsupportedType "StructDeclaration"

encodeTypeDeclaration :: Cs.TypeDeclaration -> A.Expr
encodeTypeDeclaration d = case d of
    Cs.TypeDeclarationClass c -> encodeClassDeclaration c
    Cs.TypeDeclarationStruct s -> encodeStructDeclaration s
    Cs.TypeDeclarationInterface i -> encodeInterfaceDeclaration i
    Cs.TypeDeclarationEnum e -> encodeEnumDeclaration e
    Cs.TypeDeclarationDelegate d -> encodeDelegateDeclaration d

encodeTypeParameterConstraintsClause :: Cs.TypeParameterConstraintsClause -> A.Expr
encodeTypeParameterConstraintsClause _ = unsupportedType "TypeParameterConstraintsClause"

encodeTypeParameterList :: Cs.TypeParameterList -> A.Expr
encodeTypeParameterList _ = unsupportedType "TypeParameterList"

encodeUsingDirective :: Cs.UsingDirective -> A.Expr
encodeUsingDirective _ = unsupportedType "UsingDirective"
