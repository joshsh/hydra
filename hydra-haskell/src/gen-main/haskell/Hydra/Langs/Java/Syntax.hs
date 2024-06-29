-- | A Java syntax module. Based on the Oracle Java SE 12 BNF:
-- |   https://docs.oracle.com/javase/specs/jls/se12/html/jls-19.html
-- | Note: all *WithComments types were added manually, rather than derived from the BNF, which does not allow for comments.

module Hydra.Langs.Java.Syntax where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

newtype Identifier = 
  Identifier {
    unIdentifier :: String}
  deriving (Eq, Ord, Read, Show)

_Identifier = (Core.Name "hydra/langs/java/syntax.Identifier")

newtype TypeIdentifier = 
  TypeIdentifier {
    unTypeIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_TypeIdentifier = (Core.Name "hydra/langs/java/syntax.TypeIdentifier")

data Literal = 
  LiteralNull  |
  LiteralInteger IntegerLiteral |
  LiteralFloatingPoint FloatingPointLiteral |
  LiteralBoolean Bool |
  LiteralCharacter Int |
  LiteralString StringLiteral
  deriving (Eq, Ord, Read, Show)

_Literal = (Core.Name "hydra/langs/java/syntax.Literal")

_Literal_null = (Core.Name "null")

_Literal_integer = (Core.Name "integer")

_Literal_floatingPoint = (Core.Name "floatingPoint")

_Literal_boolean = (Core.Name "boolean")

_Literal_character = (Core.Name "character")

_Literal_string = (Core.Name "string")

-- | Note: this is an approximation which ignores encoding
newtype IntegerLiteral = 
  IntegerLiteral {
    -- | Note: this is an approximation which ignores encoding
    unIntegerLiteral :: Integer}
  deriving (Eq, Ord, Read, Show)

_IntegerLiteral = (Core.Name "hydra/langs/java/syntax.IntegerLiteral")

-- | Note: this is an approximation which ignores encoding
newtype FloatingPointLiteral = 
  FloatingPointLiteral {
    -- | Note: this is an approximation which ignores encoding
    unFloatingPointLiteral :: Double}
  deriving (Eq, Ord, Read, Show)

_FloatingPointLiteral = (Core.Name "hydra/langs/java/syntax.FloatingPointLiteral")

-- | Note: this is an approximation which ignores encoding
newtype StringLiteral = 
  StringLiteral {
    -- | Note: this is an approximation which ignores encoding
    unStringLiteral :: String}
  deriving (Eq, Ord, Read, Show)

_StringLiteral = (Core.Name "hydra/langs/java/syntax.StringLiteral")

data Type = 
  TypePrimitive PrimitiveTypeWithAnnotations |
  TypeReference ReferenceType
  deriving (Eq, Ord, Read, Show)

_Type = (Core.Name "hydra/langs/java/syntax.Type")

_Type_primitive = (Core.Name "primitive")

_Type_reference = (Core.Name "reference")

data PrimitiveTypeWithAnnotations = 
  PrimitiveTypeWithAnnotations {
    primitiveTypeWithAnnotationsType :: PrimitiveType,
    primitiveTypeWithAnnotationsAnnotations :: [Annotation]}
  deriving (Eq, Ord, Read, Show)

_PrimitiveTypeWithAnnotations = (Core.Name "hydra/langs/java/syntax.PrimitiveTypeWithAnnotations")

_PrimitiveTypeWithAnnotations_type = (Core.Name "type")

_PrimitiveTypeWithAnnotations_annotations = (Core.Name "annotations")

data PrimitiveType = 
  PrimitiveTypeNumeric NumericType |
  PrimitiveTypeBoolean 
  deriving (Eq, Ord, Read, Show)

_PrimitiveType = (Core.Name "hydra/langs/java/syntax.PrimitiveType")

_PrimitiveType_numeric = (Core.Name "numeric")

_PrimitiveType_boolean = (Core.Name "boolean")

data NumericType = 
  NumericTypeIntegral IntegralType |
  NumericTypeFloatingPoint FloatingPointType
  deriving (Eq, Ord, Read, Show)

_NumericType = (Core.Name "hydra/langs/java/syntax.NumericType")

_NumericType_integral = (Core.Name "integral")

_NumericType_floatingPoint = (Core.Name "floatingPoint")

data IntegralType = 
  IntegralTypeByte  |
  IntegralTypeShort  |
  IntegralTypeInt  |
  IntegralTypeLong  |
  IntegralTypeChar 
  deriving (Eq, Ord, Read, Show)

_IntegralType = (Core.Name "hydra/langs/java/syntax.IntegralType")

_IntegralType_byte = (Core.Name "byte")

_IntegralType_short = (Core.Name "short")

_IntegralType_int = (Core.Name "int")

_IntegralType_long = (Core.Name "long")

_IntegralType_char = (Core.Name "char")

data FloatingPointType = 
  FloatingPointTypeFloat  |
  FloatingPointTypeDouble 
  deriving (Eq, Ord, Read, Show)

_FloatingPointType = (Core.Name "hydra/langs/java/syntax.FloatingPointType")

_FloatingPointType_float = (Core.Name "float")

_FloatingPointType_double = (Core.Name "double")

data ReferenceType = 
  ReferenceTypeClassOrInterface ClassOrInterfaceType |
  ReferenceTypeVariable TypeVariable |
  ReferenceTypeArray ArrayType
  deriving (Eq, Ord, Read, Show)

_ReferenceType = (Core.Name "hydra/langs/java/syntax.ReferenceType")

_ReferenceType_classOrInterface = (Core.Name "classOrInterface")

_ReferenceType_variable = (Core.Name "variable")

_ReferenceType_array = (Core.Name "array")

data ClassOrInterfaceType = 
  ClassOrInterfaceTypeClass ClassType |
  ClassOrInterfaceTypeInterface InterfaceType
  deriving (Eq, Ord, Read, Show)

_ClassOrInterfaceType = (Core.Name "hydra/langs/java/syntax.ClassOrInterfaceType")

_ClassOrInterfaceType_class = (Core.Name "class")

_ClassOrInterfaceType_interface = (Core.Name "interface")

data ClassType = 
  ClassType {
    classTypeAnnotations :: [Annotation],
    classTypeQualifier :: ClassTypeQualifier,
    classTypeIdentifier :: TypeIdentifier,
    classTypeArguments :: [TypeArgument]}
  deriving (Eq, Ord, Read, Show)

_ClassType = (Core.Name "hydra/langs/java/syntax.ClassType")

_ClassType_annotations = (Core.Name "annotations")

_ClassType_qualifier = (Core.Name "qualifier")

_ClassType_identifier = (Core.Name "identifier")

_ClassType_arguments = (Core.Name "arguments")

data ClassTypeQualifier = 
  ClassTypeQualifierNone  |
  ClassTypeQualifierPackage PackageName |
  ClassTypeQualifierParent ClassOrInterfaceType
  deriving (Eq, Ord, Read, Show)

_ClassTypeQualifier = (Core.Name "hydra/langs/java/syntax.ClassTypeQualifier")

_ClassTypeQualifier_none = (Core.Name "none")

_ClassTypeQualifier_package = (Core.Name "package")

_ClassTypeQualifier_parent = (Core.Name "parent")

newtype InterfaceType = 
  InterfaceType {
    unInterfaceType :: ClassType}
  deriving (Eq, Ord, Read, Show)

_InterfaceType = (Core.Name "hydra/langs/java/syntax.InterfaceType")

data TypeVariable = 
  TypeVariable {
    typeVariableAnnotations :: [Annotation],
    typeVariableIdentifier :: TypeIdentifier}
  deriving (Eq, Ord, Read, Show)

_TypeVariable = (Core.Name "hydra/langs/java/syntax.TypeVariable")

_TypeVariable_annotations = (Core.Name "annotations")

_TypeVariable_identifier = (Core.Name "identifier")

data ArrayType = 
  ArrayType {
    arrayTypeDims :: Dims,
    arrayTypeVariant :: ArrayType_Variant}
  deriving (Eq, Ord, Read, Show)

_ArrayType = (Core.Name "hydra/langs/java/syntax.ArrayType")

_ArrayType_dims = (Core.Name "dims")

_ArrayType_variant = (Core.Name "variant")

data ArrayType_Variant = 
  ArrayType_VariantPrimitive PrimitiveTypeWithAnnotations |
  ArrayType_VariantClassOrInterface ClassOrInterfaceType |
  ArrayType_VariantVariable TypeVariable
  deriving (Eq, Ord, Read, Show)

_ArrayType_Variant = (Core.Name "hydra/langs/java/syntax.ArrayType.Variant")

_ArrayType_Variant_primitive = (Core.Name "primitive")

_ArrayType_Variant_classOrInterface = (Core.Name "classOrInterface")

_ArrayType_Variant_variable = (Core.Name "variable")

newtype Dims = 
  Dims {
    unDims :: [[Annotation]]}
  deriving (Eq, Ord, Read, Show)

_Dims = (Core.Name "hydra/langs/java/syntax.Dims")

data TypeParameter = 
  TypeParameter {
    typeParameterModifiers :: [TypeParameterModifier],
    typeParameterIdentifier :: TypeIdentifier,
    typeParameterBound :: (Maybe TypeBound)}
  deriving (Eq, Ord, Read, Show)

_TypeParameter = (Core.Name "hydra/langs/java/syntax.TypeParameter")

_TypeParameter_modifiers = (Core.Name "modifiers")

_TypeParameter_identifier = (Core.Name "identifier")

_TypeParameter_bound = (Core.Name "bound")

newtype TypeParameterModifier = 
  TypeParameterModifier {
    unTypeParameterModifier :: Annotation}
  deriving (Eq, Ord, Read, Show)

_TypeParameterModifier = (Core.Name "hydra/langs/java/syntax.TypeParameterModifier")

data TypeBound = 
  TypeBoundVariable TypeVariable |
  TypeBoundClassOrInterface TypeBound_ClassOrInterface
  deriving (Eq, Ord, Read, Show)

_TypeBound = (Core.Name "hydra/langs/java/syntax.TypeBound")

_TypeBound_variable = (Core.Name "variable")

_TypeBound_classOrInterface = (Core.Name "classOrInterface")

data TypeBound_ClassOrInterface = 
  TypeBound_ClassOrInterface {
    typeBound_ClassOrInterfaceType :: ClassOrInterfaceType,
    typeBound_ClassOrInterfaceAdditional :: [AdditionalBound]}
  deriving (Eq, Ord, Read, Show)

_TypeBound_ClassOrInterface = (Core.Name "hydra/langs/java/syntax.TypeBound.ClassOrInterface")

_TypeBound_ClassOrInterface_type = (Core.Name "type")

_TypeBound_ClassOrInterface_additional = (Core.Name "additional")

newtype AdditionalBound = 
  AdditionalBound {
    unAdditionalBound :: InterfaceType}
  deriving (Eq, Ord, Read, Show)

_AdditionalBound = (Core.Name "hydra/langs/java/syntax.AdditionalBound")

data TypeArgument = 
  TypeArgumentReference ReferenceType |
  TypeArgumentWildcard Wildcard
  deriving (Eq, Ord, Read, Show)

_TypeArgument = (Core.Name "hydra/langs/java/syntax.TypeArgument")

_TypeArgument_reference = (Core.Name "reference")

_TypeArgument_wildcard = (Core.Name "wildcard")

data Wildcard = 
  Wildcard {
    wildcardAnnotations :: [Annotation],
    wildcardWildcard :: (Maybe WildcardBounds)}
  deriving (Eq, Ord, Read, Show)

_Wildcard = (Core.Name "hydra/langs/java/syntax.Wildcard")

_Wildcard_annotations = (Core.Name "annotations")

_Wildcard_wildcard = (Core.Name "wildcard")

data WildcardBounds = 
  WildcardBoundsExtends ReferenceType |
  WildcardBoundsSuper ReferenceType
  deriving (Eq, Ord, Read, Show)

_WildcardBounds = (Core.Name "hydra/langs/java/syntax.WildcardBounds")

_WildcardBounds_extends = (Core.Name "extends")

_WildcardBounds_super = (Core.Name "super")

data ModuleName = 
  ModuleName {
    moduleNameIdentifier :: Identifier,
    moduleNameName :: (Maybe ModuleName)}
  deriving (Eq, Ord, Read, Show)

_ModuleName = (Core.Name "hydra/langs/java/syntax.ModuleName")

_ModuleName_identifier = (Core.Name "identifier")

_ModuleName_name = (Core.Name "name")

newtype PackageName = 
  PackageName {
    unPackageName :: [Identifier]}
  deriving (Eq, Ord, Read, Show)

_PackageName = (Core.Name "hydra/langs/java/syntax.PackageName")

data TypeName = 
  TypeName {
    typeNameIdentifier :: TypeIdentifier,
    typeNameQualifier :: (Maybe PackageOrTypeName)}
  deriving (Eq, Ord, Read, Show)

_TypeName = (Core.Name "hydra/langs/java/syntax.TypeName")

_TypeName_identifier = (Core.Name "identifier")

_TypeName_qualifier = (Core.Name "qualifier")

data ExpressionName = 
  ExpressionName {
    expressionNameQualifier :: (Maybe AmbiguousName),
    expressionNameIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_ExpressionName = (Core.Name "hydra/langs/java/syntax.ExpressionName")

_ExpressionName_qualifier = (Core.Name "qualifier")

_ExpressionName_identifier = (Core.Name "identifier")

newtype MethodName = 
  MethodName {
    unMethodName :: Identifier}
  deriving (Eq, Ord, Read, Show)

_MethodName = (Core.Name "hydra/langs/java/syntax.MethodName")

newtype PackageOrTypeName = 
  PackageOrTypeName {
    unPackageOrTypeName :: [Identifier]}
  deriving (Eq, Ord, Read, Show)

_PackageOrTypeName = (Core.Name "hydra/langs/java/syntax.PackageOrTypeName")

newtype AmbiguousName = 
  AmbiguousName {
    unAmbiguousName :: [Identifier]}
  deriving (Eq, Ord, Read, Show)

_AmbiguousName = (Core.Name "hydra/langs/java/syntax.AmbiguousName")

data CompilationUnit = 
  CompilationUnitOrdinary OrdinaryCompilationUnit |
  CompilationUnitModular ModularCompilationUnit
  deriving (Eq, Ord, Read, Show)

_CompilationUnit = (Core.Name "hydra/langs/java/syntax.CompilationUnit")

_CompilationUnit_ordinary = (Core.Name "ordinary")

_CompilationUnit_modular = (Core.Name "modular")

data OrdinaryCompilationUnit = 
  OrdinaryCompilationUnit {
    ordinaryCompilationUnitPackage :: (Maybe PackageDeclaration),
    ordinaryCompilationUnitImports :: [ImportDeclaration],
    ordinaryCompilationUnitTypes :: [TypeDeclarationWithComments]}
  deriving (Eq, Ord, Read, Show)

_OrdinaryCompilationUnit = (Core.Name "hydra/langs/java/syntax.OrdinaryCompilationUnit")

_OrdinaryCompilationUnit_package = (Core.Name "package")

_OrdinaryCompilationUnit_imports = (Core.Name "imports")

_OrdinaryCompilationUnit_types = (Core.Name "types")

data ModularCompilationUnit = 
  ModularCompilationUnit {
    modularCompilationUnitImports :: [ImportDeclaration],
    modularCompilationUnitModule :: ModuleDeclaration}
  deriving (Eq, Ord, Read, Show)

_ModularCompilationUnit = (Core.Name "hydra/langs/java/syntax.ModularCompilationUnit")

_ModularCompilationUnit_imports = (Core.Name "imports")

_ModularCompilationUnit_module = (Core.Name "module")

data PackageDeclaration = 
  PackageDeclaration {
    packageDeclarationModifiers :: [PackageModifier],
    packageDeclarationIdentifiers :: [Identifier]}
  deriving (Eq, Ord, Read, Show)

_PackageDeclaration = (Core.Name "hydra/langs/java/syntax.PackageDeclaration")

_PackageDeclaration_modifiers = (Core.Name "modifiers")

_PackageDeclaration_identifiers = (Core.Name "identifiers")

newtype PackageModifier = 
  PackageModifier {
    unPackageModifier :: Annotation}
  deriving (Eq, Ord, Read, Show)

_PackageModifier = (Core.Name "hydra/langs/java/syntax.PackageModifier")

data ImportDeclaration = 
  ImportDeclarationSingleType SingleTypeImportDeclaration |
  ImportDeclarationTypeImportOnDemand TypeImportOnDemandDeclaration |
  ImportDeclarationSingleStaticImport SingleStaticImportDeclaration |
  ImportDeclarationStaticImportOnDemand StaticImportOnDemandDeclaration
  deriving (Eq, Ord, Read, Show)

_ImportDeclaration = (Core.Name "hydra/langs/java/syntax.ImportDeclaration")

_ImportDeclaration_singleType = (Core.Name "singleType")

_ImportDeclaration_typeImportOnDemand = (Core.Name "typeImportOnDemand")

_ImportDeclaration_singleStaticImport = (Core.Name "singleStaticImport")

_ImportDeclaration_staticImportOnDemand = (Core.Name "staticImportOnDemand")

newtype SingleTypeImportDeclaration = 
  SingleTypeImportDeclaration {
    unSingleTypeImportDeclaration :: TypeName}
  deriving (Eq, Ord, Read, Show)

_SingleTypeImportDeclaration = (Core.Name "hydra/langs/java/syntax.SingleTypeImportDeclaration")

newtype TypeImportOnDemandDeclaration = 
  TypeImportOnDemandDeclaration {
    unTypeImportOnDemandDeclaration :: PackageOrTypeName}
  deriving (Eq, Ord, Read, Show)

_TypeImportOnDemandDeclaration = (Core.Name "hydra/langs/java/syntax.TypeImportOnDemandDeclaration")

data SingleStaticImportDeclaration = 
  SingleStaticImportDeclaration {
    singleStaticImportDeclarationTypeName :: TypeName,
    singleStaticImportDeclarationIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_SingleStaticImportDeclaration = (Core.Name "hydra/langs/java/syntax.SingleStaticImportDeclaration")

_SingleStaticImportDeclaration_typeName = (Core.Name "typeName")

_SingleStaticImportDeclaration_identifier = (Core.Name "identifier")

newtype StaticImportOnDemandDeclaration = 
  StaticImportOnDemandDeclaration {
    unStaticImportOnDemandDeclaration :: TypeName}
  deriving (Eq, Ord, Read, Show)

_StaticImportOnDemandDeclaration = (Core.Name "hydra/langs/java/syntax.StaticImportOnDemandDeclaration")

data TypeDeclaration = 
  TypeDeclarationClass ClassDeclaration |
  TypeDeclarationInterface InterfaceDeclaration |
  TypeDeclarationNone 
  deriving (Eq, Ord, Read, Show)

_TypeDeclaration = (Core.Name "hydra/langs/java/syntax.TypeDeclaration")

_TypeDeclaration_class = (Core.Name "class")

_TypeDeclaration_interface = (Core.Name "interface")

_TypeDeclaration_none = (Core.Name "none")

data TypeDeclarationWithComments = 
  TypeDeclarationWithComments {
    typeDeclarationWithCommentsValue :: TypeDeclaration,
    typeDeclarationWithCommentsComments :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_TypeDeclarationWithComments = (Core.Name "hydra/langs/java/syntax.TypeDeclarationWithComments")

_TypeDeclarationWithComments_value = (Core.Name "value")

_TypeDeclarationWithComments_comments = (Core.Name "comments")

data ModuleDeclaration = 
  ModuleDeclaration {
    moduleDeclarationAnnotations :: [Annotation],
    moduleDeclarationOpen :: Bool,
    moduleDeclarationIdentifiers :: [Identifier],
    moduleDeclarationDirectives :: [[ModuleDirective]]}
  deriving (Eq, Ord, Read, Show)

_ModuleDeclaration = (Core.Name "hydra/langs/java/syntax.ModuleDeclaration")

_ModuleDeclaration_annotations = (Core.Name "annotations")

_ModuleDeclaration_open = (Core.Name "open")

_ModuleDeclaration_identifiers = (Core.Name "identifiers")

_ModuleDeclaration_directives = (Core.Name "directives")

data ModuleDirective = 
  ModuleDirectiveRequires ModuleDirective_Requires |
  ModuleDirectiveExports ModuleDirective_ExportsOrOpens |
  ModuleDirectiveOpens ModuleDirective_ExportsOrOpens |
  ModuleDirectiveUses TypeName |
  ModuleDirectiveProvides ModuleDirective_Provides
  deriving (Eq, Ord, Read, Show)

_ModuleDirective = (Core.Name "hydra/langs/java/syntax.ModuleDirective")

_ModuleDirective_requires = (Core.Name "requires")

_ModuleDirective_exports = (Core.Name "exports")

_ModuleDirective_opens = (Core.Name "opens")

_ModuleDirective_uses = (Core.Name "uses")

_ModuleDirective_provides = (Core.Name "provides")

data ModuleDirective_Requires = 
  ModuleDirective_Requires {
    moduleDirective_RequiresModifiers :: [RequiresModifier],
    moduleDirective_RequiresModule :: ModuleName}
  deriving (Eq, Ord, Read, Show)

_ModuleDirective_Requires = (Core.Name "hydra/langs/java/syntax.ModuleDirective.Requires")

_ModuleDirective_Requires_modifiers = (Core.Name "modifiers")

_ModuleDirective_Requires_module = (Core.Name "module")

data ModuleDirective_ExportsOrOpens = 
  ModuleDirective_ExportsOrOpens {
    moduleDirective_ExportsOrOpensPackage :: PackageName,
    -- | At least one module
    moduleDirective_ExportsOrOpensModules :: [ModuleName]}
  deriving (Eq, Ord, Read, Show)

_ModuleDirective_ExportsOrOpens = (Core.Name "hydra/langs/java/syntax.ModuleDirective.ExportsOrOpens")

_ModuleDirective_ExportsOrOpens_package = (Core.Name "package")

_ModuleDirective_ExportsOrOpens_modules = (Core.Name "modules")

data ModuleDirective_Provides = 
  ModuleDirective_Provides {
    moduleDirective_ProvidesTo :: TypeName,
    -- | At least one type
    moduleDirective_ProvidesWith :: [TypeName]}
  deriving (Eq, Ord, Read, Show)

_ModuleDirective_Provides = (Core.Name "hydra/langs/java/syntax.ModuleDirective.Provides")

_ModuleDirective_Provides_to = (Core.Name "to")

_ModuleDirective_Provides_with = (Core.Name "with")

data RequiresModifier = 
  RequiresModifierTransitive  |
  RequiresModifierStatic 
  deriving (Eq, Ord, Read, Show)

_RequiresModifier = (Core.Name "hydra/langs/java/syntax.RequiresModifier")

_RequiresModifier_transitive = (Core.Name "transitive")

_RequiresModifier_static = (Core.Name "static")

data ClassDeclaration = 
  ClassDeclarationNormal NormalClassDeclaration |
  ClassDeclarationEnum EnumDeclaration
  deriving (Eq, Ord, Read, Show)

_ClassDeclaration = (Core.Name "hydra/langs/java/syntax.ClassDeclaration")

_ClassDeclaration_normal = (Core.Name "normal")

_ClassDeclaration_enum = (Core.Name "enum")

data NormalClassDeclaration = 
  NormalClassDeclaration {
    normalClassDeclarationModifiers :: [ClassModifier],
    normalClassDeclarationIdentifier :: TypeIdentifier,
    normalClassDeclarationParameters :: [TypeParameter],
    normalClassDeclarationExtends :: (Maybe ClassType),
    normalClassDeclarationImplements :: [InterfaceType],
    normalClassDeclarationBody :: ClassBody}
  deriving (Eq, Ord, Read, Show)

_NormalClassDeclaration = (Core.Name "hydra/langs/java/syntax.NormalClassDeclaration")

_NormalClassDeclaration_modifiers = (Core.Name "modifiers")

_NormalClassDeclaration_identifier = (Core.Name "identifier")

_NormalClassDeclaration_parameters = (Core.Name "parameters")

_NormalClassDeclaration_extends = (Core.Name "extends")

_NormalClassDeclaration_implements = (Core.Name "implements")

_NormalClassDeclaration_body = (Core.Name "body")

data ClassModifier = 
  ClassModifierAnnotation Annotation |
  ClassModifierPublic  |
  ClassModifierProtected  |
  ClassModifierPrivate  |
  ClassModifierAbstract  |
  ClassModifierStatic  |
  ClassModifierFinal  |
  ClassModifierStrictfp 
  deriving (Eq, Ord, Read, Show)

_ClassModifier = (Core.Name "hydra/langs/java/syntax.ClassModifier")

_ClassModifier_annotation = (Core.Name "annotation")

_ClassModifier_public = (Core.Name "public")

_ClassModifier_protected = (Core.Name "protected")

_ClassModifier_private = (Core.Name "private")

_ClassModifier_abstract = (Core.Name "abstract")

_ClassModifier_static = (Core.Name "static")

_ClassModifier_final = (Core.Name "final")

_ClassModifier_strictfp = (Core.Name "strictfp")

newtype ClassBody = 
  ClassBody {
    unClassBody :: [ClassBodyDeclarationWithComments]}
  deriving (Eq, Ord, Read, Show)

_ClassBody = (Core.Name "hydra/langs/java/syntax.ClassBody")

data ClassBodyDeclaration = 
  ClassBodyDeclarationClassMember ClassMemberDeclaration |
  ClassBodyDeclarationInstanceInitializer InstanceInitializer |
  ClassBodyDeclarationStaticInitializer StaticInitializer |
  ClassBodyDeclarationConstructorDeclaration ConstructorDeclaration
  deriving (Eq, Ord, Read, Show)

_ClassBodyDeclaration = (Core.Name "hydra/langs/java/syntax.ClassBodyDeclaration")

_ClassBodyDeclaration_classMember = (Core.Name "classMember")

_ClassBodyDeclaration_instanceInitializer = (Core.Name "instanceInitializer")

_ClassBodyDeclaration_staticInitializer = (Core.Name "staticInitializer")

_ClassBodyDeclaration_constructorDeclaration = (Core.Name "constructorDeclaration")

data ClassBodyDeclarationWithComments = 
  ClassBodyDeclarationWithComments {
    classBodyDeclarationWithCommentsValue :: ClassBodyDeclaration,
    classBodyDeclarationWithCommentsComments :: (Maybe String)}
  deriving (Eq, Ord, Read, Show)

_ClassBodyDeclarationWithComments = (Core.Name "hydra/langs/java/syntax.ClassBodyDeclarationWithComments")

_ClassBodyDeclarationWithComments_value = (Core.Name "value")

_ClassBodyDeclarationWithComments_comments = (Core.Name "comments")

data ClassMemberDeclaration = 
  ClassMemberDeclarationField FieldDeclaration |
  ClassMemberDeclarationMethod MethodDeclaration |
  ClassMemberDeclarationClass ClassDeclaration |
  ClassMemberDeclarationInterface InterfaceDeclaration |
  ClassMemberDeclarationNone 
  deriving (Eq, Ord, Read, Show)

_ClassMemberDeclaration = (Core.Name "hydra/langs/java/syntax.ClassMemberDeclaration")

_ClassMemberDeclaration_field = (Core.Name "field")

_ClassMemberDeclaration_method = (Core.Name "method")

_ClassMemberDeclaration_class = (Core.Name "class")

_ClassMemberDeclaration_interface = (Core.Name "interface")

_ClassMemberDeclaration_none = (Core.Name "none")

data FieldDeclaration = 
  FieldDeclaration {
    fieldDeclarationModifiers :: [FieldModifier],
    fieldDeclarationUnannType :: UnannType,
    fieldDeclarationVariableDeclarators :: [VariableDeclarator]}
  deriving (Eq, Ord, Read, Show)

_FieldDeclaration = (Core.Name "hydra/langs/java/syntax.FieldDeclaration")

_FieldDeclaration_modifiers = (Core.Name "modifiers")

_FieldDeclaration_unannType = (Core.Name "unannType")

_FieldDeclaration_variableDeclarators = (Core.Name "variableDeclarators")

data FieldModifier = 
  FieldModifierAnnotation Annotation |
  FieldModifierPublic  |
  FieldModifierProtected  |
  FieldModifierPrivate  |
  FieldModifierStatic  |
  FieldModifierFinal  |
  FieldModifierTransient  |
  FieldModifierVolatile 
  deriving (Eq, Ord, Read, Show)

_FieldModifier = (Core.Name "hydra/langs/java/syntax.FieldModifier")

_FieldModifier_annotation = (Core.Name "annotation")

_FieldModifier_public = (Core.Name "public")

_FieldModifier_protected = (Core.Name "protected")

_FieldModifier_private = (Core.Name "private")

_FieldModifier_static = (Core.Name "static")

_FieldModifier_final = (Core.Name "final")

_FieldModifier_transient = (Core.Name "transient")

_FieldModifier_volatile = (Core.Name "volatile")

data VariableDeclarator = 
  VariableDeclarator {
    variableDeclaratorId :: VariableDeclaratorId,
    variableDeclaratorInitializer :: (Maybe VariableInitializer)}
  deriving (Eq, Ord, Read, Show)

_VariableDeclarator = (Core.Name "hydra/langs/java/syntax.VariableDeclarator")

_VariableDeclarator_id = (Core.Name "id")

_VariableDeclarator_initializer = (Core.Name "initializer")

data VariableDeclaratorId = 
  VariableDeclaratorId {
    variableDeclaratorIdIdentifier :: Identifier,
    variableDeclaratorIdDims :: (Maybe Dims)}
  deriving (Eq, Ord, Read, Show)

_VariableDeclaratorId = (Core.Name "hydra/langs/java/syntax.VariableDeclaratorId")

_VariableDeclaratorId_identifier = (Core.Name "identifier")

_VariableDeclaratorId_dims = (Core.Name "dims")

data VariableInitializer = 
  VariableInitializerExpression Expression |
  VariableInitializerArrayInitializer ArrayInitializer
  deriving (Eq, Ord, Read, Show)

_VariableInitializer = (Core.Name "hydra/langs/java/syntax.VariableInitializer")

_VariableInitializer_expression = (Core.Name "expression")

_VariableInitializer_arrayInitializer = (Core.Name "arrayInitializer")

-- | A Type which does not allow annotations
newtype UnannType = 
  UnannType {
    -- | A Type which does not allow annotations
    unUnannType :: Type}
  deriving (Eq, Ord, Read, Show)

_UnannType = (Core.Name "hydra/langs/java/syntax.UnannType")

-- | A ClassType which does not allow annotations
newtype UnannClassType = 
  UnannClassType {
    -- | A ClassType which does not allow annotations
    unUnannClassType :: ClassType}
  deriving (Eq, Ord, Read, Show)

_UnannClassType = (Core.Name "hydra/langs/java/syntax.UnannClassType")

data MethodDeclaration = 
  MethodDeclaration {
    -- | Note: simple methods cannot have annotations
    methodDeclarationAnnotations :: [Annotation],
    methodDeclarationModifiers :: [MethodModifier],
    methodDeclarationHeader :: MethodHeader,
    methodDeclarationBody :: MethodBody}
  deriving (Eq, Ord, Read, Show)

_MethodDeclaration = (Core.Name "hydra/langs/java/syntax.MethodDeclaration")

_MethodDeclaration_annotations = (Core.Name "annotations")

_MethodDeclaration_modifiers = (Core.Name "modifiers")

_MethodDeclaration_header = (Core.Name "header")

_MethodDeclaration_body = (Core.Name "body")

data MethodModifier = 
  MethodModifierAnnotation Annotation |
  MethodModifierPublic  |
  MethodModifierProtected  |
  MethodModifierPrivate  |
  MethodModifierAbstract  |
  MethodModifierStatic  |
  MethodModifierFinal  |
  MethodModifierSynchronized  |
  MethodModifierNative  |
  MethodModifierStrictfb 
  deriving (Eq, Ord, Read, Show)

_MethodModifier = (Core.Name "hydra/langs/java/syntax.MethodModifier")

_MethodModifier_annotation = (Core.Name "annotation")

_MethodModifier_public = (Core.Name "public")

_MethodModifier_protected = (Core.Name "protected")

_MethodModifier_private = (Core.Name "private")

_MethodModifier_abstract = (Core.Name "abstract")

_MethodModifier_static = (Core.Name "static")

_MethodModifier_final = (Core.Name "final")

_MethodModifier_synchronized = (Core.Name "synchronized")

_MethodModifier_native = (Core.Name "native")

_MethodModifier_strictfb = (Core.Name "strictfb")

data MethodHeader = 
  MethodHeader {
    methodHeaderParameters :: [TypeParameter],
    methodHeaderResult :: Result,
    methodHeaderDeclarator :: MethodDeclarator,
    methodHeaderThrows :: (Maybe Throws)}
  deriving (Eq, Ord, Read, Show)

_MethodHeader = (Core.Name "hydra/langs/java/syntax.MethodHeader")

_MethodHeader_parameters = (Core.Name "parameters")

_MethodHeader_result = (Core.Name "result")

_MethodHeader_declarator = (Core.Name "declarator")

_MethodHeader_throws = (Core.Name "throws")

data Result = 
  ResultType UnannType |
  ResultVoid 
  deriving (Eq, Ord, Read, Show)

_Result = (Core.Name "hydra/langs/java/syntax.Result")

_Result_type = (Core.Name "type")

_Result_void = (Core.Name "void")

data MethodDeclarator = 
  MethodDeclarator {
    methodDeclaratorIdentifier :: Identifier,
    methodDeclaratorReceiverParameter :: (Maybe ReceiverParameter),
    methodDeclaratorFormalParameters :: [FormalParameter]}
  deriving (Eq, Ord, Read, Show)

_MethodDeclarator = (Core.Name "hydra/langs/java/syntax.MethodDeclarator")

_MethodDeclarator_identifier = (Core.Name "identifier")

_MethodDeclarator_receiverParameter = (Core.Name "receiverParameter")

_MethodDeclarator_formalParameters = (Core.Name "formalParameters")

data ReceiverParameter = 
  ReceiverParameter {
    receiverParameterAnnotations :: [Annotation],
    receiverParameterUnannType :: UnannType,
    receiverParameterIdentifier :: (Maybe Identifier)}
  deriving (Eq, Ord, Read, Show)

_ReceiverParameter = (Core.Name "hydra/langs/java/syntax.ReceiverParameter")

_ReceiverParameter_annotations = (Core.Name "annotations")

_ReceiverParameter_unannType = (Core.Name "unannType")

_ReceiverParameter_identifier = (Core.Name "identifier")

data FormalParameter = 
  FormalParameterSimple FormalParameter_Simple |
  FormalParameterVariableArity VariableArityParameter
  deriving (Eq, Ord, Read, Show)

_FormalParameter = (Core.Name "hydra/langs/java/syntax.FormalParameter")

_FormalParameter_simple = (Core.Name "simple")

_FormalParameter_variableArity = (Core.Name "variableArity")

data FormalParameter_Simple = 
  FormalParameter_Simple {
    formalParameter_SimpleModifiers :: [VariableModifier],
    formalParameter_SimpleType :: UnannType,
    formalParameter_SimpleId :: VariableDeclaratorId}
  deriving (Eq, Ord, Read, Show)

_FormalParameter_Simple = (Core.Name "hydra/langs/java/syntax.FormalParameter.Simple")

_FormalParameter_Simple_modifiers = (Core.Name "modifiers")

_FormalParameter_Simple_type = (Core.Name "type")

_FormalParameter_Simple_id = (Core.Name "id")

data VariableArityParameter = 
  VariableArityParameter {
    variableArityParameterModifiers :: VariableModifier,
    variableArityParameterType :: UnannType,
    variableArityParameterAnnotations :: [Annotation],
    variableArityParameterIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_VariableArityParameter = (Core.Name "hydra/langs/java/syntax.VariableArityParameter")

_VariableArityParameter_modifiers = (Core.Name "modifiers")

_VariableArityParameter_type = (Core.Name "type")

_VariableArityParameter_annotations = (Core.Name "annotations")

_VariableArityParameter_identifier = (Core.Name "identifier")

data VariableModifier = 
  VariableModifierAnnotation Annotation |
  VariableModifierFinal 
  deriving (Eq, Ord, Read, Show)

_VariableModifier = (Core.Name "hydra/langs/java/syntax.VariableModifier")

_VariableModifier_annotation = (Core.Name "annotation")

_VariableModifier_final = (Core.Name "final")

newtype Throws = 
  Throws {
    unThrows :: [ExceptionType]}
  deriving (Eq, Ord, Read, Show)

_Throws = (Core.Name "hydra/langs/java/syntax.Throws")

data ExceptionType = 
  ExceptionTypeClass ClassType |
  ExceptionTypeVariable TypeVariable
  deriving (Eq, Ord, Read, Show)

_ExceptionType = (Core.Name "hydra/langs/java/syntax.ExceptionType")

_ExceptionType_class = (Core.Name "class")

_ExceptionType_variable = (Core.Name "variable")

data MethodBody = 
  MethodBodyBlock Block |
  MethodBodyNone 
  deriving (Eq, Ord, Read, Show)

_MethodBody = (Core.Name "hydra/langs/java/syntax.MethodBody")

_MethodBody_block = (Core.Name "block")

_MethodBody_none = (Core.Name "none")

newtype InstanceInitializer = 
  InstanceInitializer {
    unInstanceInitializer :: Block}
  deriving (Eq, Ord, Read, Show)

_InstanceInitializer = (Core.Name "hydra/langs/java/syntax.InstanceInitializer")

newtype StaticInitializer = 
  StaticInitializer {
    unStaticInitializer :: Block}
  deriving (Eq, Ord, Read, Show)

_StaticInitializer = (Core.Name "hydra/langs/java/syntax.StaticInitializer")

data ConstructorDeclaration = 
  ConstructorDeclaration {
    constructorDeclarationModifiers :: [ConstructorModifier],
    constructorDeclarationConstructor :: ConstructorDeclarator,
    constructorDeclarationThrows :: (Maybe Throws),
    constructorDeclarationBody :: ConstructorBody}
  deriving (Eq, Ord, Read, Show)

_ConstructorDeclaration = (Core.Name "hydra/langs/java/syntax.ConstructorDeclaration")

_ConstructorDeclaration_modifiers = (Core.Name "modifiers")

_ConstructorDeclaration_constructor = (Core.Name "constructor")

_ConstructorDeclaration_throws = (Core.Name "throws")

_ConstructorDeclaration_body = (Core.Name "body")

data ConstructorModifier = 
  ConstructorModifierAnnotation Annotation |
  ConstructorModifierPublic  |
  ConstructorModifierProtected  |
  ConstructorModifierPrivate 
  deriving (Eq, Ord, Read, Show)

_ConstructorModifier = (Core.Name "hydra/langs/java/syntax.ConstructorModifier")

_ConstructorModifier_annotation = (Core.Name "annotation")

_ConstructorModifier_public = (Core.Name "public")

_ConstructorModifier_protected = (Core.Name "protected")

_ConstructorModifier_private = (Core.Name "private")

data ConstructorDeclarator = 
  ConstructorDeclarator {
    constructorDeclaratorParameters :: [TypeParameter],
    constructorDeclaratorName :: SimpleTypeName,
    constructorDeclaratorReceiverParameter :: (Maybe ReceiverParameter),
    constructorDeclaratorFormalParameters :: [FormalParameter]}
  deriving (Eq, Ord, Read, Show)

_ConstructorDeclarator = (Core.Name "hydra/langs/java/syntax.ConstructorDeclarator")

_ConstructorDeclarator_parameters = (Core.Name "parameters")

_ConstructorDeclarator_name = (Core.Name "name")

_ConstructorDeclarator_receiverParameter = (Core.Name "receiverParameter")

_ConstructorDeclarator_formalParameters = (Core.Name "formalParameters")

newtype SimpleTypeName = 
  SimpleTypeName {
    unSimpleTypeName :: TypeIdentifier}
  deriving (Eq, Ord, Read, Show)

_SimpleTypeName = (Core.Name "hydra/langs/java/syntax.SimpleTypeName")

data ConstructorBody = 
  ConstructorBody {
    constructorBodyInvocation :: (Maybe ExplicitConstructorInvocation),
    constructorBodyStatements :: [BlockStatement]}
  deriving (Eq, Ord, Read, Show)

_ConstructorBody = (Core.Name "hydra/langs/java/syntax.ConstructorBody")

_ConstructorBody_invocation = (Core.Name "invocation")

_ConstructorBody_statements = (Core.Name "statements")

data ExplicitConstructorInvocation = 
  ExplicitConstructorInvocation {
    explicitConstructorInvocationTypeArguments :: [TypeArgument],
    explicitConstructorInvocationArguments :: [Expression],
    explicitConstructorInvocationVariant :: ExplicitConstructorInvocation_Variant}
  deriving (Eq, Ord, Read, Show)

_ExplicitConstructorInvocation = (Core.Name "hydra/langs/java/syntax.ExplicitConstructorInvocation")

_ExplicitConstructorInvocation_typeArguments = (Core.Name "typeArguments")

_ExplicitConstructorInvocation_arguments = (Core.Name "arguments")

_ExplicitConstructorInvocation_variant = (Core.Name "variant")

data ExplicitConstructorInvocation_Variant = 
  ExplicitConstructorInvocation_VariantThis  |
  ExplicitConstructorInvocation_VariantSuper (Maybe ExpressionName) |
  ExplicitConstructorInvocation_VariantPrimary Primary
  deriving (Eq, Ord, Read, Show)

_ExplicitConstructorInvocation_Variant = (Core.Name "hydra/langs/java/syntax.ExplicitConstructorInvocation.Variant")

_ExplicitConstructorInvocation_Variant_this = (Core.Name "this")

_ExplicitConstructorInvocation_Variant_super = (Core.Name "super")

_ExplicitConstructorInvocation_Variant_primary = (Core.Name "primary")

data EnumDeclaration = 
  EnumDeclaration {
    enumDeclarationModifiers :: [ClassModifier],
    enumDeclarationIdentifier :: TypeIdentifier,
    enumDeclarationImplements :: [InterfaceType],
    enumDeclarationBody :: EnumBody}
  deriving (Eq, Ord, Read, Show)

_EnumDeclaration = (Core.Name "hydra/langs/java/syntax.EnumDeclaration")

_EnumDeclaration_modifiers = (Core.Name "modifiers")

_EnumDeclaration_identifier = (Core.Name "identifier")

_EnumDeclaration_implements = (Core.Name "implements")

_EnumDeclaration_body = (Core.Name "body")

newtype EnumBody = 
  EnumBody {
    unEnumBody :: [EnumBody_Element]}
  deriving (Eq, Ord, Read, Show)

_EnumBody = (Core.Name "hydra/langs/java/syntax.EnumBody")

data EnumBody_Element = 
  EnumBody_Element {
    enumBody_ElementConstants :: [EnumConstant],
    enumBody_ElementBodyDeclarations :: [ClassBodyDeclaration]}
  deriving (Eq, Ord, Read, Show)

_EnumBody_Element = (Core.Name "hydra/langs/java/syntax.EnumBody.Element")

_EnumBody_Element_constants = (Core.Name "constants")

_EnumBody_Element_bodyDeclarations = (Core.Name "bodyDeclarations")

data EnumConstant = 
  EnumConstant {
    enumConstantModifiers :: [EnumConstantModifier],
    enumConstantIdentifier :: Identifier,
    enumConstantArguments :: [[Expression]],
    enumConstantBody :: (Maybe ClassBody)}
  deriving (Eq, Ord, Read, Show)

_EnumConstant = (Core.Name "hydra/langs/java/syntax.EnumConstant")

_EnumConstant_modifiers = (Core.Name "modifiers")

_EnumConstant_identifier = (Core.Name "identifier")

_EnumConstant_arguments = (Core.Name "arguments")

_EnumConstant_body = (Core.Name "body")

newtype EnumConstantModifier = 
  EnumConstantModifier {
    unEnumConstantModifier :: Annotation}
  deriving (Eq, Ord, Read, Show)

_EnumConstantModifier = (Core.Name "hydra/langs/java/syntax.EnumConstantModifier")

data InterfaceDeclaration = 
  InterfaceDeclarationNormalInterface NormalInterfaceDeclaration |
  InterfaceDeclarationAnnotationType AnnotationTypeDeclaration
  deriving (Eq, Ord, Read, Show)

_InterfaceDeclaration = (Core.Name "hydra/langs/java/syntax.InterfaceDeclaration")

_InterfaceDeclaration_normalInterface = (Core.Name "normalInterface")

_InterfaceDeclaration_annotationType = (Core.Name "annotationType")

data NormalInterfaceDeclaration = 
  NormalInterfaceDeclaration {
    normalInterfaceDeclarationModifiers :: [InterfaceModifier],
    normalInterfaceDeclarationIdentifier :: TypeIdentifier,
    normalInterfaceDeclarationParameters :: [TypeParameter],
    normalInterfaceDeclarationExtends :: [InterfaceType],
    normalInterfaceDeclarationBody :: InterfaceBody}
  deriving (Eq, Ord, Read, Show)

_NormalInterfaceDeclaration = (Core.Name "hydra/langs/java/syntax.NormalInterfaceDeclaration")

_NormalInterfaceDeclaration_modifiers = (Core.Name "modifiers")

_NormalInterfaceDeclaration_identifier = (Core.Name "identifier")

_NormalInterfaceDeclaration_parameters = (Core.Name "parameters")

_NormalInterfaceDeclaration_extends = (Core.Name "extends")

_NormalInterfaceDeclaration_body = (Core.Name "body")

data InterfaceModifier = 
  InterfaceModifierAnnotation Annotation |
  InterfaceModifierPublic  |
  InterfaceModifierProtected  |
  InterfaceModifierPrivate  |
  InterfaceModifierAbstract  |
  InterfaceModifierStatic  |
  InterfaceModifierStrictfb 
  deriving (Eq, Ord, Read, Show)

_InterfaceModifier = (Core.Name "hydra/langs/java/syntax.InterfaceModifier")

_InterfaceModifier_annotation = (Core.Name "annotation")

_InterfaceModifier_public = (Core.Name "public")

_InterfaceModifier_protected = (Core.Name "protected")

_InterfaceModifier_private = (Core.Name "private")

_InterfaceModifier_abstract = (Core.Name "abstract")

_InterfaceModifier_static = (Core.Name "static")

_InterfaceModifier_strictfb = (Core.Name "strictfb")

newtype InterfaceBody = 
  InterfaceBody {
    unInterfaceBody :: [InterfaceMemberDeclaration]}
  deriving (Eq, Ord, Read, Show)

_InterfaceBody = (Core.Name "hydra/langs/java/syntax.InterfaceBody")

data InterfaceMemberDeclaration = 
  InterfaceMemberDeclarationConstant ConstantDeclaration |
  InterfaceMemberDeclarationInterfaceMethod InterfaceMethodDeclaration |
  InterfaceMemberDeclarationClass ClassDeclaration |
  InterfaceMemberDeclarationInterface InterfaceDeclaration
  deriving (Eq, Ord, Read, Show)

_InterfaceMemberDeclaration = (Core.Name "hydra/langs/java/syntax.InterfaceMemberDeclaration")

_InterfaceMemberDeclaration_constant = (Core.Name "constant")

_InterfaceMemberDeclaration_interfaceMethod = (Core.Name "interfaceMethod")

_InterfaceMemberDeclaration_class = (Core.Name "class")

_InterfaceMemberDeclaration_interface = (Core.Name "interface")

data ConstantDeclaration = 
  ConstantDeclaration {
    constantDeclarationModifiers :: [ConstantModifier],
    constantDeclarationType :: UnannType,
    constantDeclarationVariables :: [VariableDeclarator]}
  deriving (Eq, Ord, Read, Show)

_ConstantDeclaration = (Core.Name "hydra/langs/java/syntax.ConstantDeclaration")

_ConstantDeclaration_modifiers = (Core.Name "modifiers")

_ConstantDeclaration_type = (Core.Name "type")

_ConstantDeclaration_variables = (Core.Name "variables")

data ConstantModifier = 
  ConstantModifierAnnotation Annotation |
  ConstantModifierPublic  |
  ConstantModifierStatic  |
  ConstantModifierFinal 
  deriving (Eq, Ord, Read, Show)

_ConstantModifier = (Core.Name "hydra/langs/java/syntax.ConstantModifier")

_ConstantModifier_annotation = (Core.Name "annotation")

_ConstantModifier_public = (Core.Name "public")

_ConstantModifier_static = (Core.Name "static")

_ConstantModifier_final = (Core.Name "final")

data InterfaceMethodDeclaration = 
  InterfaceMethodDeclaration {
    interfaceMethodDeclarationModifiers :: [InterfaceMethodModifier],
    interfaceMethodDeclarationHeader :: MethodHeader,
    interfaceMethodDeclarationBody :: MethodBody}
  deriving (Eq, Ord, Read, Show)

_InterfaceMethodDeclaration = (Core.Name "hydra/langs/java/syntax.InterfaceMethodDeclaration")

_InterfaceMethodDeclaration_modifiers = (Core.Name "modifiers")

_InterfaceMethodDeclaration_header = (Core.Name "header")

_InterfaceMethodDeclaration_body = (Core.Name "body")

data InterfaceMethodModifier = 
  InterfaceMethodModifierAnnotation Annotation |
  InterfaceMethodModifierPublic  |
  InterfaceMethodModifierPrivate  |
  InterfaceMethodModifierAbstract  |
  InterfaceMethodModifierDefault  |
  InterfaceMethodModifierStatic  |
  InterfaceMethodModifierStrictfp 
  deriving (Eq, Ord, Read, Show)

_InterfaceMethodModifier = (Core.Name "hydra/langs/java/syntax.InterfaceMethodModifier")

_InterfaceMethodModifier_annotation = (Core.Name "annotation")

_InterfaceMethodModifier_public = (Core.Name "public")

_InterfaceMethodModifier_private = (Core.Name "private")

_InterfaceMethodModifier_abstract = (Core.Name "abstract")

_InterfaceMethodModifier_default = (Core.Name "default")

_InterfaceMethodModifier_static = (Core.Name "static")

_InterfaceMethodModifier_strictfp = (Core.Name "strictfp")

data AnnotationTypeDeclaration = 
  AnnotationTypeDeclaration {
    annotationTypeDeclarationModifiers :: [InterfaceModifier],
    annotationTypeDeclarationIdentifier :: TypeIdentifier,
    annotationTypeDeclarationBody :: AnnotationTypeBody}
  deriving (Eq, Ord, Read, Show)

_AnnotationTypeDeclaration = (Core.Name "hydra/langs/java/syntax.AnnotationTypeDeclaration")

_AnnotationTypeDeclaration_modifiers = (Core.Name "modifiers")

_AnnotationTypeDeclaration_identifier = (Core.Name "identifier")

_AnnotationTypeDeclaration_body = (Core.Name "body")

newtype AnnotationTypeBody = 
  AnnotationTypeBody {
    unAnnotationTypeBody :: [[AnnotationTypeMemberDeclaration]]}
  deriving (Eq, Ord, Read, Show)

_AnnotationTypeBody = (Core.Name "hydra/langs/java/syntax.AnnotationTypeBody")

data AnnotationTypeMemberDeclaration = 
  AnnotationTypeMemberDeclarationAnnotationType AnnotationTypeElementDeclaration |
  AnnotationTypeMemberDeclarationConstant ConstantDeclaration |
  AnnotationTypeMemberDeclarationClass ClassDeclaration |
  AnnotationTypeMemberDeclarationInterface InterfaceDeclaration
  deriving (Eq, Ord, Read, Show)

_AnnotationTypeMemberDeclaration = (Core.Name "hydra/langs/java/syntax.AnnotationTypeMemberDeclaration")

_AnnotationTypeMemberDeclaration_annotationType = (Core.Name "annotationType")

_AnnotationTypeMemberDeclaration_constant = (Core.Name "constant")

_AnnotationTypeMemberDeclaration_class = (Core.Name "class")

_AnnotationTypeMemberDeclaration_interface = (Core.Name "interface")

data AnnotationTypeElementDeclaration = 
  AnnotationTypeElementDeclaration {
    annotationTypeElementDeclarationModifiers :: [AnnotationTypeElementModifier],
    annotationTypeElementDeclarationType :: UnannType,
    annotationTypeElementDeclarationIdentifier :: Identifier,
    annotationTypeElementDeclarationDims :: (Maybe Dims),
    annotationTypeElementDeclarationDefault :: (Maybe DefaultValue)}
  deriving (Eq, Ord, Read, Show)

_AnnotationTypeElementDeclaration = (Core.Name "hydra/langs/java/syntax.AnnotationTypeElementDeclaration")

_AnnotationTypeElementDeclaration_modifiers = (Core.Name "modifiers")

_AnnotationTypeElementDeclaration_type = (Core.Name "type")

_AnnotationTypeElementDeclaration_identifier = (Core.Name "identifier")

_AnnotationTypeElementDeclaration_dims = (Core.Name "dims")

_AnnotationTypeElementDeclaration_default = (Core.Name "default")

data AnnotationTypeElementModifier = 
  AnnotationTypeElementModifierPublic Annotation |
  AnnotationTypeElementModifierAbstract 
  deriving (Eq, Ord, Read, Show)

_AnnotationTypeElementModifier = (Core.Name "hydra/langs/java/syntax.AnnotationTypeElementModifier")

_AnnotationTypeElementModifier_public = (Core.Name "public")

_AnnotationTypeElementModifier_abstract = (Core.Name "abstract")

newtype DefaultValue = 
  DefaultValue {
    unDefaultValue :: ElementValue}
  deriving (Eq, Ord, Read, Show)

_DefaultValue = (Core.Name "hydra/langs/java/syntax.DefaultValue")

data Annotation = 
  AnnotationNormal NormalAnnotation |
  AnnotationMarker MarkerAnnotation |
  AnnotationSingleElement SingleElementAnnotation
  deriving (Eq, Ord, Read, Show)

_Annotation = (Core.Name "hydra/langs/java/syntax.Annotation")

_Annotation_normal = (Core.Name "normal")

_Annotation_marker = (Core.Name "marker")

_Annotation_singleElement = (Core.Name "singleElement")

data NormalAnnotation = 
  NormalAnnotation {
    normalAnnotationTypeName :: TypeName,
    normalAnnotationPairs :: [ElementValuePair]}
  deriving (Eq, Ord, Read, Show)

_NormalAnnotation = (Core.Name "hydra/langs/java/syntax.NormalAnnotation")

_NormalAnnotation_typeName = (Core.Name "typeName")

_NormalAnnotation_pairs = (Core.Name "pairs")

data ElementValuePair = 
  ElementValuePair {
    elementValuePairKey :: Identifier,
    elementValuePairValue :: ElementValue}
  deriving (Eq, Ord, Read, Show)

_ElementValuePair = (Core.Name "hydra/langs/java/syntax.ElementValuePair")

_ElementValuePair_key = (Core.Name "key")

_ElementValuePair_value = (Core.Name "value")

data ElementValue = 
  ElementValueConditionalExpression ConditionalExpression |
  ElementValueElementValueArrayInitializer ElementValueArrayInitializer |
  ElementValueAnnotation Annotation
  deriving (Eq, Ord, Read, Show)

_ElementValue = (Core.Name "hydra/langs/java/syntax.ElementValue")

_ElementValue_conditionalExpression = (Core.Name "conditionalExpression")

_ElementValue_elementValueArrayInitializer = (Core.Name "elementValueArrayInitializer")

_ElementValue_annotation = (Core.Name "annotation")

newtype ElementValueArrayInitializer = 
  ElementValueArrayInitializer {
    unElementValueArrayInitializer :: [ElementValue]}
  deriving (Eq, Ord, Read, Show)

_ElementValueArrayInitializer = (Core.Name "hydra/langs/java/syntax.ElementValueArrayInitializer")

newtype MarkerAnnotation = 
  MarkerAnnotation {
    unMarkerAnnotation :: TypeName}
  deriving (Eq, Ord, Read, Show)

_MarkerAnnotation = (Core.Name "hydra/langs/java/syntax.MarkerAnnotation")

data SingleElementAnnotation = 
  SingleElementAnnotation {
    singleElementAnnotationName :: TypeName,
    singleElementAnnotationValue :: (Maybe ElementValue)}
  deriving (Eq, Ord, Read, Show)

_SingleElementAnnotation = (Core.Name "hydra/langs/java/syntax.SingleElementAnnotation")

_SingleElementAnnotation_name = (Core.Name "name")

_SingleElementAnnotation_value = (Core.Name "value")

newtype ArrayInitializer = 
  ArrayInitializer {
    unArrayInitializer :: [[VariableInitializer]]}
  deriving (Eq, Ord, Read, Show)

_ArrayInitializer = (Core.Name "hydra/langs/java/syntax.ArrayInitializer")

newtype Block = 
  Block {
    unBlock :: [BlockStatement]}
  deriving (Eq, Ord, Read, Show)

_Block = (Core.Name "hydra/langs/java/syntax.Block")

data BlockStatement = 
  BlockStatementLocalVariableDeclaration LocalVariableDeclarationStatement |
  BlockStatementClass ClassDeclaration |
  BlockStatementStatement Statement
  deriving (Eq, Ord, Read, Show)

_BlockStatement = (Core.Name "hydra/langs/java/syntax.BlockStatement")

_BlockStatement_localVariableDeclaration = (Core.Name "localVariableDeclaration")

_BlockStatement_class = (Core.Name "class")

_BlockStatement_statement = (Core.Name "statement")

newtype LocalVariableDeclarationStatement = 
  LocalVariableDeclarationStatement {
    unLocalVariableDeclarationStatement :: LocalVariableDeclaration}
  deriving (Eq, Ord, Read, Show)

_LocalVariableDeclarationStatement = (Core.Name "hydra/langs/java/syntax.LocalVariableDeclarationStatement")

data LocalVariableDeclaration = 
  LocalVariableDeclaration {
    localVariableDeclarationModifiers :: [VariableModifier],
    localVariableDeclarationType :: LocalVariableType,
    localVariableDeclarationDeclarators :: [VariableDeclarator]}
  deriving (Eq, Ord, Read, Show)

_LocalVariableDeclaration = (Core.Name "hydra/langs/java/syntax.LocalVariableDeclaration")

_LocalVariableDeclaration_modifiers = (Core.Name "modifiers")

_LocalVariableDeclaration_type = (Core.Name "type")

_LocalVariableDeclaration_declarators = (Core.Name "declarators")

data LocalVariableType = 
  LocalVariableTypeType UnannType |
  LocalVariableTypeVar 
  deriving (Eq, Ord, Read, Show)

_LocalVariableType = (Core.Name "hydra/langs/java/syntax.LocalVariableType")

_LocalVariableType_type = (Core.Name "type")

_LocalVariableType_var = (Core.Name "var")

data Statement = 
  StatementWithoutTrailing StatementWithoutTrailingSubstatement |
  StatementLabeled LabeledStatement |
  StatementIfThen IfThenStatement |
  StatementIfThenElse IfThenElseStatement |
  StatementWhile WhileStatement |
  StatementFor ForStatement
  deriving (Eq, Ord, Read, Show)

_Statement = (Core.Name "hydra/langs/java/syntax.Statement")

_Statement_withoutTrailing = (Core.Name "withoutTrailing")

_Statement_labeled = (Core.Name "labeled")

_Statement_ifThen = (Core.Name "ifThen")

_Statement_ifThenElse = (Core.Name "ifThenElse")

_Statement_while = (Core.Name "while")

_Statement_for = (Core.Name "for")

data StatementNoShortIf = 
  StatementNoShortIfWithoutTrailing StatementWithoutTrailingSubstatement |
  StatementNoShortIfLabeled LabeledStatementNoShortIf |
  StatementNoShortIfIfThenElse IfThenElseStatementNoShortIf |
  StatementNoShortIfWhile WhileStatementNoShortIf |
  StatementNoShortIfFor ForStatementNoShortIf
  deriving (Eq, Ord, Read, Show)

_StatementNoShortIf = (Core.Name "hydra/langs/java/syntax.StatementNoShortIf")

_StatementNoShortIf_withoutTrailing = (Core.Name "withoutTrailing")

_StatementNoShortIf_labeled = (Core.Name "labeled")

_StatementNoShortIf_ifThenElse = (Core.Name "ifThenElse")

_StatementNoShortIf_while = (Core.Name "while")

_StatementNoShortIf_for = (Core.Name "for")

data StatementWithoutTrailingSubstatement = 
  StatementWithoutTrailingSubstatementBlock Block |
  StatementWithoutTrailingSubstatementEmpty EmptyStatement |
  StatementWithoutTrailingSubstatementExpression ExpressionStatement |
  StatementWithoutTrailingSubstatementAssert AssertStatement |
  StatementWithoutTrailingSubstatementSwitch SwitchStatement |
  StatementWithoutTrailingSubstatementDo DoStatement |
  StatementWithoutTrailingSubstatementBreak BreakStatement |
  StatementWithoutTrailingSubstatementContinue ContinueStatement |
  StatementWithoutTrailingSubstatementReturn ReturnStatement |
  StatementWithoutTrailingSubstatementSynchronized SynchronizedStatement |
  StatementWithoutTrailingSubstatementThrow ThrowStatement |
  StatementWithoutTrailingSubstatementTry TryStatement
  deriving (Eq, Ord, Read, Show)

_StatementWithoutTrailingSubstatement = (Core.Name "hydra/langs/java/syntax.StatementWithoutTrailingSubstatement")

_StatementWithoutTrailingSubstatement_block = (Core.Name "block")

_StatementWithoutTrailingSubstatement_empty = (Core.Name "empty")

_StatementWithoutTrailingSubstatement_expression = (Core.Name "expression")

_StatementWithoutTrailingSubstatement_assert = (Core.Name "assert")

_StatementWithoutTrailingSubstatement_switch = (Core.Name "switch")

_StatementWithoutTrailingSubstatement_do = (Core.Name "do")

_StatementWithoutTrailingSubstatement_break = (Core.Name "break")

_StatementWithoutTrailingSubstatement_continue = (Core.Name "continue")

_StatementWithoutTrailingSubstatement_return = (Core.Name "return")

_StatementWithoutTrailingSubstatement_synchronized = (Core.Name "synchronized")

_StatementWithoutTrailingSubstatement_throw = (Core.Name "throw")

_StatementWithoutTrailingSubstatement_try = (Core.Name "try")

data EmptyStatement = 
  EmptyStatement {}
  deriving (Eq, Ord, Read, Show)

_EmptyStatement = (Core.Name "hydra/langs/java/syntax.EmptyStatement")

data LabeledStatement = 
  LabeledStatement {
    labeledStatementIdentifier :: Identifier,
    labeledStatementStatement :: Statement}
  deriving (Eq, Ord, Read, Show)

_LabeledStatement = (Core.Name "hydra/langs/java/syntax.LabeledStatement")

_LabeledStatement_identifier = (Core.Name "identifier")

_LabeledStatement_statement = (Core.Name "statement")

data LabeledStatementNoShortIf = 
  LabeledStatementNoShortIf {
    labeledStatementNoShortIfIdentifier :: Identifier,
    labeledStatementNoShortIfStatement :: StatementNoShortIf}
  deriving (Eq, Ord, Read, Show)

_LabeledStatementNoShortIf = (Core.Name "hydra/langs/java/syntax.LabeledStatementNoShortIf")

_LabeledStatementNoShortIf_identifier = (Core.Name "identifier")

_LabeledStatementNoShortIf_statement = (Core.Name "statement")

newtype ExpressionStatement = 
  ExpressionStatement {
    unExpressionStatement :: StatementExpression}
  deriving (Eq, Ord, Read, Show)

_ExpressionStatement = (Core.Name "hydra/langs/java/syntax.ExpressionStatement")

data StatementExpression = 
  StatementExpressionAssignment Assignment |
  StatementExpressionPreIncrement PreIncrementExpression |
  StatementExpressionPreDecrement PreDecrementExpression |
  StatementExpressionPostIncrement PostIncrementExpression |
  StatementExpressionPostDecrement PostDecrementExpression |
  StatementExpressionMethodInvocation MethodInvocation |
  StatementExpressionClassInstanceCreation ClassInstanceCreationExpression
  deriving (Eq, Ord, Read, Show)

_StatementExpression = (Core.Name "hydra/langs/java/syntax.StatementExpression")

_StatementExpression_assignment = (Core.Name "assignment")

_StatementExpression_preIncrement = (Core.Name "preIncrement")

_StatementExpression_preDecrement = (Core.Name "preDecrement")

_StatementExpression_postIncrement = (Core.Name "postIncrement")

_StatementExpression_postDecrement = (Core.Name "postDecrement")

_StatementExpression_methodInvocation = (Core.Name "methodInvocation")

_StatementExpression_classInstanceCreation = (Core.Name "classInstanceCreation")

data IfThenStatement = 
  IfThenStatement {
    ifThenStatementExpression :: Expression,
    ifThenStatementStatement :: Statement}
  deriving (Eq, Ord, Read, Show)

_IfThenStatement = (Core.Name "hydra/langs/java/syntax.IfThenStatement")

_IfThenStatement_expression = (Core.Name "expression")

_IfThenStatement_statement = (Core.Name "statement")

data IfThenElseStatement = 
  IfThenElseStatement {
    ifThenElseStatementCond :: (Maybe Expression),
    ifThenElseStatementThen :: StatementNoShortIf,
    ifThenElseStatementElse :: Statement}
  deriving (Eq, Ord, Read, Show)

_IfThenElseStatement = (Core.Name "hydra/langs/java/syntax.IfThenElseStatement")

_IfThenElseStatement_cond = (Core.Name "cond")

_IfThenElseStatement_then = (Core.Name "then")

_IfThenElseStatement_else = (Core.Name "else")

data IfThenElseStatementNoShortIf = 
  IfThenElseStatementNoShortIf {
    ifThenElseStatementNoShortIfCond :: (Maybe Expression),
    ifThenElseStatementNoShortIfThen :: StatementNoShortIf,
    ifThenElseStatementNoShortIfElse :: StatementNoShortIf}
  deriving (Eq, Ord, Read, Show)

_IfThenElseStatementNoShortIf = (Core.Name "hydra/langs/java/syntax.IfThenElseStatementNoShortIf")

_IfThenElseStatementNoShortIf_cond = (Core.Name "cond")

_IfThenElseStatementNoShortIf_then = (Core.Name "then")

_IfThenElseStatementNoShortIf_else = (Core.Name "else")

data AssertStatement = 
  AssertStatementSingle Expression |
  AssertStatementPair AssertStatement_Pair
  deriving (Eq, Ord, Read, Show)

_AssertStatement = (Core.Name "hydra/langs/java/syntax.AssertStatement")

_AssertStatement_single = (Core.Name "single")

_AssertStatement_pair = (Core.Name "pair")

data AssertStatement_Pair = 
  AssertStatement_Pair {
    assertStatement_PairFirst :: Expression,
    assertStatement_PairSecond :: Expression}
  deriving (Eq, Ord, Read, Show)

_AssertStatement_Pair = (Core.Name "hydra/langs/java/syntax.AssertStatement.Pair")

_AssertStatement_Pair_first = (Core.Name "first")

_AssertStatement_Pair_second = (Core.Name "second")

data SwitchStatement = 
  SwitchStatement {
    switchStatementCond :: Expression,
    switchStatementBlock :: SwitchBlock}
  deriving (Eq, Ord, Read, Show)

_SwitchStatement = (Core.Name "hydra/langs/java/syntax.SwitchStatement")

_SwitchStatement_cond = (Core.Name "cond")

_SwitchStatement_block = (Core.Name "block")

newtype SwitchBlock = 
  SwitchBlock {
    unSwitchBlock :: [SwitchBlock_Pair]}
  deriving (Eq, Ord, Read, Show)

_SwitchBlock = (Core.Name "hydra/langs/java/syntax.SwitchBlock")

data SwitchBlock_Pair = 
  SwitchBlock_Pair {
    switchBlock_PairStatements :: [SwitchBlockStatementGroup],
    switchBlock_PairLabels :: [SwitchLabel]}
  deriving (Eq, Ord, Read, Show)

_SwitchBlock_Pair = (Core.Name "hydra/langs/java/syntax.SwitchBlock.Pair")

_SwitchBlock_Pair_statements = (Core.Name "statements")

_SwitchBlock_Pair_labels = (Core.Name "labels")

data SwitchBlockStatementGroup = 
  SwitchBlockStatementGroup {
    switchBlockStatementGroupLabels :: [SwitchLabel],
    switchBlockStatementGroupStatements :: [BlockStatement]}
  deriving (Eq, Ord, Read, Show)

_SwitchBlockStatementGroup = (Core.Name "hydra/langs/java/syntax.SwitchBlockStatementGroup")

_SwitchBlockStatementGroup_labels = (Core.Name "labels")

_SwitchBlockStatementGroup_statements = (Core.Name "statements")

data SwitchLabel = 
  SwitchLabelConstant ConstantExpression |
  SwitchLabelEnumConstant EnumConstantName |
  SwitchLabelDefault 
  deriving (Eq, Ord, Read, Show)

_SwitchLabel = (Core.Name "hydra/langs/java/syntax.SwitchLabel")

_SwitchLabel_constant = (Core.Name "constant")

_SwitchLabel_enumConstant = (Core.Name "enumConstant")

_SwitchLabel_default = (Core.Name "default")

newtype EnumConstantName = 
  EnumConstantName {
    unEnumConstantName :: Identifier}
  deriving (Eq, Ord, Read, Show)

_EnumConstantName = (Core.Name "hydra/langs/java/syntax.EnumConstantName")

data WhileStatement = 
  WhileStatement {
    whileStatementCond :: (Maybe Expression),
    whileStatementBody :: Statement}
  deriving (Eq, Ord, Read, Show)

_WhileStatement = (Core.Name "hydra/langs/java/syntax.WhileStatement")

_WhileStatement_cond = (Core.Name "cond")

_WhileStatement_body = (Core.Name "body")

data WhileStatementNoShortIf = 
  WhileStatementNoShortIf {
    whileStatementNoShortIfCond :: (Maybe Expression),
    whileStatementNoShortIfBody :: StatementNoShortIf}
  deriving (Eq, Ord, Read, Show)

_WhileStatementNoShortIf = (Core.Name "hydra/langs/java/syntax.WhileStatementNoShortIf")

_WhileStatementNoShortIf_cond = (Core.Name "cond")

_WhileStatementNoShortIf_body = (Core.Name "body")

data DoStatement = 
  DoStatement {
    doStatementBody :: Statement,
    doStatementConde :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_DoStatement = (Core.Name "hydra/langs/java/syntax.DoStatement")

_DoStatement_body = (Core.Name "body")

_DoStatement_conde = (Core.Name "conde")

data ForStatement = 
  ForStatementBasic BasicForStatement |
  ForStatementEnhanced EnhancedForStatement
  deriving (Eq, Ord, Read, Show)

_ForStatement = (Core.Name "hydra/langs/java/syntax.ForStatement")

_ForStatement_basic = (Core.Name "basic")

_ForStatement_enhanced = (Core.Name "enhanced")

data ForStatementNoShortIf = 
  ForStatementNoShortIfBasic BasicForStatementNoShortIf |
  ForStatementNoShortIfEnhanced EnhancedForStatementNoShortIf
  deriving (Eq, Ord, Read, Show)

_ForStatementNoShortIf = (Core.Name "hydra/langs/java/syntax.ForStatementNoShortIf")

_ForStatementNoShortIf_basic = (Core.Name "basic")

_ForStatementNoShortIf_enhanced = (Core.Name "enhanced")

data BasicForStatement = 
  BasicForStatement {
    basicForStatementCond :: ForCond,
    basicForStatementBody :: Statement}
  deriving (Eq, Ord, Read, Show)

_BasicForStatement = (Core.Name "hydra/langs/java/syntax.BasicForStatement")

_BasicForStatement_cond = (Core.Name "cond")

_BasicForStatement_body = (Core.Name "body")

data ForCond = 
  ForCond {
    forCondInit :: (Maybe ForInit),
    forCondCond :: (Maybe Expression),
    forCondUpdate :: (Maybe ForUpdate)}
  deriving (Eq, Ord, Read, Show)

_ForCond = (Core.Name "hydra/langs/java/syntax.ForCond")

_ForCond_init = (Core.Name "init")

_ForCond_cond = (Core.Name "cond")

_ForCond_update = (Core.Name "update")

data BasicForStatementNoShortIf = 
  BasicForStatementNoShortIf {
    basicForStatementNoShortIfCond :: ForCond,
    basicForStatementNoShortIfBody :: StatementNoShortIf}
  deriving (Eq, Ord, Read, Show)

_BasicForStatementNoShortIf = (Core.Name "hydra/langs/java/syntax.BasicForStatementNoShortIf")

_BasicForStatementNoShortIf_cond = (Core.Name "cond")

_BasicForStatementNoShortIf_body = (Core.Name "body")

data ForInit = 
  ForInitStatements [StatementExpression] |
  ForInitLocalVariable LocalVariableDeclaration
  deriving (Eq, Ord, Read, Show)

_ForInit = (Core.Name "hydra/langs/java/syntax.ForInit")

_ForInit_statements = (Core.Name "statements")

_ForInit_localVariable = (Core.Name "localVariable")

newtype ForUpdate = 
  ForUpdate {
    unForUpdate :: [StatementExpression]}
  deriving (Eq, Ord, Read, Show)

_ForUpdate = (Core.Name "hydra/langs/java/syntax.ForUpdate")

data EnhancedForStatement = 
  EnhancedForStatement {
    enhancedForStatementCond :: EnhancedForCond,
    enhancedForStatementBody :: Statement}
  deriving (Eq, Ord, Read, Show)

_EnhancedForStatement = (Core.Name "hydra/langs/java/syntax.EnhancedForStatement")

_EnhancedForStatement_cond = (Core.Name "cond")

_EnhancedForStatement_body = (Core.Name "body")

data EnhancedForCond = 
  EnhancedForCond {
    enhancedForCondModifiers :: [VariableModifier],
    enhancedForCondType :: LocalVariableType,
    enhancedForCondId :: VariableDeclaratorId,
    enhancedForCondExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_EnhancedForCond = (Core.Name "hydra/langs/java/syntax.EnhancedForCond")

_EnhancedForCond_modifiers = (Core.Name "modifiers")

_EnhancedForCond_type = (Core.Name "type")

_EnhancedForCond_id = (Core.Name "id")

_EnhancedForCond_expression = (Core.Name "expression")

data EnhancedForStatementNoShortIf = 
  EnhancedForStatementNoShortIf {
    enhancedForStatementNoShortIfCond :: EnhancedForCond,
    enhancedForStatementNoShortIfBody :: StatementNoShortIf}
  deriving (Eq, Ord, Read, Show)

_EnhancedForStatementNoShortIf = (Core.Name "hydra/langs/java/syntax.EnhancedForStatementNoShortIf")

_EnhancedForStatementNoShortIf_cond = (Core.Name "cond")

_EnhancedForStatementNoShortIf_body = (Core.Name "body")

newtype BreakStatement = 
  BreakStatement {
    unBreakStatement :: (Maybe Identifier)}
  deriving (Eq, Ord, Read, Show)

_BreakStatement = (Core.Name "hydra/langs/java/syntax.BreakStatement")

newtype ContinueStatement = 
  ContinueStatement {
    unContinueStatement :: (Maybe Identifier)}
  deriving (Eq, Ord, Read, Show)

_ContinueStatement = (Core.Name "hydra/langs/java/syntax.ContinueStatement")

newtype ReturnStatement = 
  ReturnStatement {
    unReturnStatement :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_ReturnStatement = (Core.Name "hydra/langs/java/syntax.ReturnStatement")

newtype ThrowStatement = 
  ThrowStatement {
    unThrowStatement :: Expression}
  deriving (Eq, Ord, Read, Show)

_ThrowStatement = (Core.Name "hydra/langs/java/syntax.ThrowStatement")

data SynchronizedStatement = 
  SynchronizedStatement {
    synchronizedStatementExpression :: Expression,
    synchronizedStatementBlock :: Block}
  deriving (Eq, Ord, Read, Show)

_SynchronizedStatement = (Core.Name "hydra/langs/java/syntax.SynchronizedStatement")

_SynchronizedStatement_expression = (Core.Name "expression")

_SynchronizedStatement_block = (Core.Name "block")

data TryStatement = 
  TryStatementSimple TryStatement_Simple |
  TryStatementWithFinally TryStatement_WithFinally |
  TryStatementWithResources TryWithResourcesStatement
  deriving (Eq, Ord, Read, Show)

_TryStatement = (Core.Name "hydra/langs/java/syntax.TryStatement")

_TryStatement_simple = (Core.Name "simple")

_TryStatement_withFinally = (Core.Name "withFinally")

_TryStatement_withResources = (Core.Name "withResources")

data TryStatement_Simple = 
  TryStatement_Simple {
    tryStatement_SimpleBlock :: Block,
    tryStatement_SimpleCatches :: Catches}
  deriving (Eq, Ord, Read, Show)

_TryStatement_Simple = (Core.Name "hydra/langs/java/syntax.TryStatement.Simple")

_TryStatement_Simple_block = (Core.Name "block")

_TryStatement_Simple_catches = (Core.Name "catches")

data TryStatement_WithFinally = 
  TryStatement_WithFinally {
    tryStatement_WithFinallyBlock :: Block,
    tryStatement_WithFinallyCatches :: (Maybe Catches),
    tryStatement_WithFinallyFinally :: Finally}
  deriving (Eq, Ord, Read, Show)

_TryStatement_WithFinally = (Core.Name "hydra/langs/java/syntax.TryStatement.WithFinally")

_TryStatement_WithFinally_block = (Core.Name "block")

_TryStatement_WithFinally_catches = (Core.Name "catches")

_TryStatement_WithFinally_finally = (Core.Name "finally")

newtype Catches = 
  Catches {
    unCatches :: [CatchClause]}
  deriving (Eq, Ord, Read, Show)

_Catches = (Core.Name "hydra/langs/java/syntax.Catches")

data CatchClause = 
  CatchClause {
    catchClauseParameter :: (Maybe CatchFormalParameter),
    catchClauseBlock :: Block}
  deriving (Eq, Ord, Read, Show)

_CatchClause = (Core.Name "hydra/langs/java/syntax.CatchClause")

_CatchClause_parameter = (Core.Name "parameter")

_CatchClause_block = (Core.Name "block")

data CatchFormalParameter = 
  CatchFormalParameter {
    catchFormalParameterModifiers :: [VariableModifier],
    catchFormalParameterType :: CatchType,
    catchFormalParameterId :: VariableDeclaratorId}
  deriving (Eq, Ord, Read, Show)

_CatchFormalParameter = (Core.Name "hydra/langs/java/syntax.CatchFormalParameter")

_CatchFormalParameter_modifiers = (Core.Name "modifiers")

_CatchFormalParameter_type = (Core.Name "type")

_CatchFormalParameter_id = (Core.Name "id")

data CatchType = 
  CatchType {
    catchTypeType :: UnannClassType,
    catchTypeTypes :: [ClassType]}
  deriving (Eq, Ord, Read, Show)

_CatchType = (Core.Name "hydra/langs/java/syntax.CatchType")

_CatchType_type = (Core.Name "type")

_CatchType_types = (Core.Name "types")

newtype Finally = 
  Finally {
    unFinally :: Block}
  deriving (Eq, Ord, Read, Show)

_Finally = (Core.Name "hydra/langs/java/syntax.Finally")

data TryWithResourcesStatement = 
  TryWithResourcesStatement {
    tryWithResourcesStatementResourceSpecification :: ResourceSpecification,
    tryWithResourcesStatementBlock :: Block,
    tryWithResourcesStatementCatches :: (Maybe Catches),
    tryWithResourcesStatementFinally :: (Maybe Finally)}
  deriving (Eq, Ord, Read, Show)

_TryWithResourcesStatement = (Core.Name "hydra/langs/java/syntax.TryWithResourcesStatement")

_TryWithResourcesStatement_resourceSpecification = (Core.Name "resourceSpecification")

_TryWithResourcesStatement_block = (Core.Name "block")

_TryWithResourcesStatement_catches = (Core.Name "catches")

_TryWithResourcesStatement_finally = (Core.Name "finally")

newtype ResourceSpecification = 
  ResourceSpecification {
    unResourceSpecification :: [Resource]}
  deriving (Eq, Ord, Read, Show)

_ResourceSpecification = (Core.Name "hydra/langs/java/syntax.ResourceSpecification")

data Resource = 
  ResourceLocal Resource_Local |
  ResourceVariable VariableAccess
  deriving (Eq, Ord, Read, Show)

_Resource = (Core.Name "hydra/langs/java/syntax.Resource")

_Resource_local = (Core.Name "local")

_Resource_variable = (Core.Name "variable")

data Resource_Local = 
  Resource_Local {
    resource_LocalModifiers :: [VariableModifier],
    resource_LocalType :: LocalVariableType,
    resource_LocalIdentifier :: Identifier,
    resource_LocalExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_Resource_Local = (Core.Name "hydra/langs/java/syntax.Resource.Local")

_Resource_Local_modifiers = (Core.Name "modifiers")

_Resource_Local_type = (Core.Name "type")

_Resource_Local_identifier = (Core.Name "identifier")

_Resource_Local_expression = (Core.Name "expression")

data VariableAccess = 
  VariableAccessExpressionName ExpressionName |
  VariableAccessFieldAccess FieldAccess
  deriving (Eq, Ord, Read, Show)

_VariableAccess = (Core.Name "hydra/langs/java/syntax.VariableAccess")

_VariableAccess_expressionName = (Core.Name "expressionName")

_VariableAccess_fieldAccess = (Core.Name "fieldAccess")

data Primary = 
  PrimaryNoNewArray PrimaryNoNewArray |
  PrimaryArrayCreation ArrayCreationExpression
  deriving (Eq, Ord, Read, Show)

_Primary = (Core.Name "hydra/langs/java/syntax.Primary")

_Primary_noNewArray = (Core.Name "noNewArray")

_Primary_arrayCreation = (Core.Name "arrayCreation")

data PrimaryNoNewArray = 
  PrimaryNoNewArrayLiteral Literal |
  PrimaryNoNewArrayClassLiteral ClassLiteral |
  PrimaryNoNewArrayThis  |
  PrimaryNoNewArrayDotThis TypeName |
  PrimaryNoNewArrayParens Expression |
  PrimaryNoNewArrayClassInstance ClassInstanceCreationExpression |
  PrimaryNoNewArrayFieldAccess FieldAccess |
  PrimaryNoNewArrayArrayAccess ArrayAccess |
  PrimaryNoNewArrayMethodInvocation MethodInvocation |
  PrimaryNoNewArrayMethodReference MethodReference
  deriving (Eq, Ord, Read, Show)

_PrimaryNoNewArray = (Core.Name "hydra/langs/java/syntax.PrimaryNoNewArray")

_PrimaryNoNewArray_literal = (Core.Name "literal")

_PrimaryNoNewArray_classLiteral = (Core.Name "classLiteral")

_PrimaryNoNewArray_this = (Core.Name "this")

_PrimaryNoNewArray_dotThis = (Core.Name "dotThis")

_PrimaryNoNewArray_parens = (Core.Name "parens")

_PrimaryNoNewArray_classInstance = (Core.Name "classInstance")

_PrimaryNoNewArray_fieldAccess = (Core.Name "fieldAccess")

_PrimaryNoNewArray_arrayAccess = (Core.Name "arrayAccess")

_PrimaryNoNewArray_methodInvocation = (Core.Name "methodInvocation")

_PrimaryNoNewArray_methodReference = (Core.Name "methodReference")

data ClassLiteral = 
  ClassLiteralType TypeNameArray |
  ClassLiteralNumericType NumericTypeArray |
  ClassLiteralBoolean BooleanArray |
  ClassLiteralVoid 
  deriving (Eq, Ord, Read, Show)

_ClassLiteral = (Core.Name "hydra/langs/java/syntax.ClassLiteral")

_ClassLiteral_type = (Core.Name "type")

_ClassLiteral_numericType = (Core.Name "numericType")

_ClassLiteral_boolean = (Core.Name "boolean")

_ClassLiteral_void = (Core.Name "void")

data TypeNameArray = 
  TypeNameArraySimple TypeName |
  TypeNameArrayArray TypeNameArray
  deriving (Eq, Ord, Read, Show)

_TypeNameArray = (Core.Name "hydra/langs/java/syntax.TypeNameArray")

_TypeNameArray_simple = (Core.Name "simple")

_TypeNameArray_array = (Core.Name "array")

data NumericTypeArray = 
  NumericTypeArraySimple NumericType |
  NumericTypeArrayArray NumericTypeArray
  deriving (Eq, Ord, Read, Show)

_NumericTypeArray = (Core.Name "hydra/langs/java/syntax.NumericTypeArray")

_NumericTypeArray_simple = (Core.Name "simple")

_NumericTypeArray_array = (Core.Name "array")

data BooleanArray = 
  BooleanArraySimple  |
  BooleanArrayArray BooleanArray
  deriving (Eq, Ord, Read, Show)

_BooleanArray = (Core.Name "hydra/langs/java/syntax.BooleanArray")

_BooleanArray_simple = (Core.Name "simple")

_BooleanArray_array = (Core.Name "array")

data ClassInstanceCreationExpression = 
  ClassInstanceCreationExpression {
    classInstanceCreationExpressionQualifier :: (Maybe ClassInstanceCreationExpression_Qualifier),
    classInstanceCreationExpressionExpression :: UnqualifiedClassInstanceCreationExpression}
  deriving (Eq, Ord, Read, Show)

_ClassInstanceCreationExpression = (Core.Name "hydra/langs/java/syntax.ClassInstanceCreationExpression")

_ClassInstanceCreationExpression_qualifier = (Core.Name "qualifier")

_ClassInstanceCreationExpression_expression = (Core.Name "expression")

data ClassInstanceCreationExpression_Qualifier = 
  ClassInstanceCreationExpression_QualifierExpression ExpressionName |
  ClassInstanceCreationExpression_QualifierPrimary Primary
  deriving (Eq, Ord, Read, Show)

_ClassInstanceCreationExpression_Qualifier = (Core.Name "hydra/langs/java/syntax.ClassInstanceCreationExpression.Qualifier")

_ClassInstanceCreationExpression_Qualifier_expression = (Core.Name "expression")

_ClassInstanceCreationExpression_Qualifier_primary = (Core.Name "primary")

data UnqualifiedClassInstanceCreationExpression = 
  UnqualifiedClassInstanceCreationExpression {
    unqualifiedClassInstanceCreationExpressionTypeArguments :: [TypeArgument],
    unqualifiedClassInstanceCreationExpressionClassOrInterface :: ClassOrInterfaceTypeToInstantiate,
    unqualifiedClassInstanceCreationExpressionArguments :: [Expression],
    unqualifiedClassInstanceCreationExpressionBody :: (Maybe ClassBody)}
  deriving (Eq, Ord, Read, Show)

_UnqualifiedClassInstanceCreationExpression = (Core.Name "hydra/langs/java/syntax.UnqualifiedClassInstanceCreationExpression")

_UnqualifiedClassInstanceCreationExpression_typeArguments = (Core.Name "typeArguments")

_UnqualifiedClassInstanceCreationExpression_classOrInterface = (Core.Name "classOrInterface")

_UnqualifiedClassInstanceCreationExpression_arguments = (Core.Name "arguments")

_UnqualifiedClassInstanceCreationExpression_body = (Core.Name "body")

data ClassOrInterfaceTypeToInstantiate = 
  ClassOrInterfaceTypeToInstantiate {
    classOrInterfaceTypeToInstantiateIdentifiers :: [AnnotatedIdentifier],
    classOrInterfaceTypeToInstantiateTypeArguments :: (Maybe TypeArgumentsOrDiamond)}
  deriving (Eq, Ord, Read, Show)

_ClassOrInterfaceTypeToInstantiate = (Core.Name "hydra/langs/java/syntax.ClassOrInterfaceTypeToInstantiate")

_ClassOrInterfaceTypeToInstantiate_identifiers = (Core.Name "identifiers")

_ClassOrInterfaceTypeToInstantiate_typeArguments = (Core.Name "typeArguments")

data AnnotatedIdentifier = 
  AnnotatedIdentifier {
    annotatedIdentifierAnnotations :: [Annotation],
    annotatedIdentifierIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_AnnotatedIdentifier = (Core.Name "hydra/langs/java/syntax.AnnotatedIdentifier")

_AnnotatedIdentifier_annotations = (Core.Name "annotations")

_AnnotatedIdentifier_identifier = (Core.Name "identifier")

data TypeArgumentsOrDiamond = 
  TypeArgumentsOrDiamondArguments [TypeArgument] |
  TypeArgumentsOrDiamondDiamond 
  deriving (Eq, Ord, Read, Show)

_TypeArgumentsOrDiamond = (Core.Name "hydra/langs/java/syntax.TypeArgumentsOrDiamond")

_TypeArgumentsOrDiamond_arguments = (Core.Name "arguments")

_TypeArgumentsOrDiamond_diamond = (Core.Name "diamond")

data FieldAccess = 
  FieldAccess {
    fieldAccessQualifier :: FieldAccess_Qualifier,
    fieldAccessIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_FieldAccess = (Core.Name "hydra/langs/java/syntax.FieldAccess")

_FieldAccess_qualifier = (Core.Name "qualifier")

_FieldAccess_identifier = (Core.Name "identifier")

data FieldAccess_Qualifier = 
  FieldAccess_QualifierPrimary Primary |
  FieldAccess_QualifierSuper  |
  FieldAccess_QualifierTyped TypeName
  deriving (Eq, Ord, Read, Show)

_FieldAccess_Qualifier = (Core.Name "hydra/langs/java/syntax.FieldAccess.Qualifier")

_FieldAccess_Qualifier_primary = (Core.Name "primary")

_FieldAccess_Qualifier_super = (Core.Name "super")

_FieldAccess_Qualifier_typed = (Core.Name "typed")

data ArrayAccess = 
  ArrayAccess {
    arrayAccessExpression :: (Maybe Expression),
    arrayAccessVariant :: ArrayAccess_Variant}
  deriving (Eq, Ord, Read, Show)

_ArrayAccess = (Core.Name "hydra/langs/java/syntax.ArrayAccess")

_ArrayAccess_expression = (Core.Name "expression")

_ArrayAccess_variant = (Core.Name "variant")

data ArrayAccess_Variant = 
  ArrayAccess_VariantName ExpressionName |
  ArrayAccess_VariantPrimary PrimaryNoNewArray
  deriving (Eq, Ord, Read, Show)

_ArrayAccess_Variant = (Core.Name "hydra/langs/java/syntax.ArrayAccess.Variant")

_ArrayAccess_Variant_name = (Core.Name "name")

_ArrayAccess_Variant_primary = (Core.Name "primary")

data MethodInvocation = 
  MethodInvocation {
    methodInvocationHeader :: MethodInvocation_Header,
    methodInvocationArguments :: [Expression]}
  deriving (Eq, Ord, Read, Show)

_MethodInvocation = (Core.Name "hydra/langs/java/syntax.MethodInvocation")

_MethodInvocation_header = (Core.Name "header")

_MethodInvocation_arguments = (Core.Name "arguments")

data MethodInvocation_Header = 
  MethodInvocation_HeaderSimple MethodName |
  MethodInvocation_HeaderComplex MethodInvocation_Complex
  deriving (Eq, Ord, Read, Show)

_MethodInvocation_Header = (Core.Name "hydra/langs/java/syntax.MethodInvocation.Header")

_MethodInvocation_Header_simple = (Core.Name "simple")

_MethodInvocation_Header_complex = (Core.Name "complex")

data MethodInvocation_Complex = 
  MethodInvocation_Complex {
    methodInvocation_ComplexVariant :: MethodInvocation_Variant,
    methodInvocation_ComplexTypeArguments :: [TypeArgument],
    methodInvocation_ComplexIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_MethodInvocation_Complex = (Core.Name "hydra/langs/java/syntax.MethodInvocation.Complex")

_MethodInvocation_Complex_variant = (Core.Name "variant")

_MethodInvocation_Complex_typeArguments = (Core.Name "typeArguments")

_MethodInvocation_Complex_identifier = (Core.Name "identifier")

data MethodInvocation_Variant = 
  MethodInvocation_VariantType TypeName |
  MethodInvocation_VariantExpression ExpressionName |
  MethodInvocation_VariantPrimary Primary |
  MethodInvocation_VariantSuper  |
  MethodInvocation_VariantTypeSuper TypeName
  deriving (Eq, Ord, Read, Show)

_MethodInvocation_Variant = (Core.Name "hydra/langs/java/syntax.MethodInvocation.Variant")

_MethodInvocation_Variant_type = (Core.Name "type")

_MethodInvocation_Variant_expression = (Core.Name "expression")

_MethodInvocation_Variant_primary = (Core.Name "primary")

_MethodInvocation_Variant_super = (Core.Name "super")

_MethodInvocation_Variant_typeSuper = (Core.Name "typeSuper")

data MethodReference = 
  MethodReferenceExpression MethodReference_Expression |
  MethodReferencePrimary MethodReference_Primary |
  MethodReferenceReferenceType MethodReference_ReferenceType |
  MethodReferenceSuper MethodReference_Super |
  MethodReferenceNew MethodReference_New |
  MethodReferenceArray MethodReference_Array
  deriving (Eq, Ord, Read, Show)

_MethodReference = (Core.Name "hydra/langs/java/syntax.MethodReference")

_MethodReference_expression = (Core.Name "expression")

_MethodReference_primary = (Core.Name "primary")

_MethodReference_referenceType = (Core.Name "referenceType")

_MethodReference_super = (Core.Name "super")

_MethodReference_new = (Core.Name "new")

_MethodReference_array = (Core.Name "array")

data MethodReference_Expression = 
  MethodReference_Expression {
    methodReference_ExpressionName :: ExpressionName,
    methodReference_ExpressionTypeArguments :: [TypeArgument],
    methodReference_ExpressionIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_MethodReference_Expression = (Core.Name "hydra/langs/java/syntax.MethodReference.Expression")

_MethodReference_Expression_name = (Core.Name "name")

_MethodReference_Expression_typeArguments = (Core.Name "typeArguments")

_MethodReference_Expression_identifier = (Core.Name "identifier")

data MethodReference_Primary = 
  MethodReference_Primary {
    methodReference_PrimaryPrimary :: Primary,
    methodReference_PrimaryTypeArguments :: [TypeArgument],
    methodReference_PrimaryIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_MethodReference_Primary = (Core.Name "hydra/langs/java/syntax.MethodReference.Primary")

_MethodReference_Primary_primary = (Core.Name "primary")

_MethodReference_Primary_typeArguments = (Core.Name "typeArguments")

_MethodReference_Primary_identifier = (Core.Name "identifier")

data MethodReference_ReferenceType = 
  MethodReference_ReferenceType {
    methodReference_ReferenceTypeReferenceType :: ReferenceType,
    methodReference_ReferenceTypeTypeArguments :: [TypeArgument],
    methodReference_ReferenceTypeIdentifier :: Identifier}
  deriving (Eq, Ord, Read, Show)

_MethodReference_ReferenceType = (Core.Name "hydra/langs/java/syntax.MethodReference.ReferenceType")

_MethodReference_ReferenceType_referenceType = (Core.Name "referenceType")

_MethodReference_ReferenceType_typeArguments = (Core.Name "typeArguments")

_MethodReference_ReferenceType_identifier = (Core.Name "identifier")

data MethodReference_Super = 
  MethodReference_Super {
    methodReference_SuperTypeArguments :: [TypeArgument],
    methodReference_SuperIdentifier :: Identifier,
    methodReference_SuperSuper :: Bool}
  deriving (Eq, Ord, Read, Show)

_MethodReference_Super = (Core.Name "hydra/langs/java/syntax.MethodReference.Super")

_MethodReference_Super_typeArguments = (Core.Name "typeArguments")

_MethodReference_Super_identifier = (Core.Name "identifier")

_MethodReference_Super_super = (Core.Name "super")

data MethodReference_New = 
  MethodReference_New {
    methodReference_NewClassType :: ClassType,
    methodReference_NewTypeArguments :: [TypeArgument]}
  deriving (Eq, Ord, Read, Show)

_MethodReference_New = (Core.Name "hydra/langs/java/syntax.MethodReference.New")

_MethodReference_New_classType = (Core.Name "classType")

_MethodReference_New_typeArguments = (Core.Name "typeArguments")

newtype MethodReference_Array = 
  MethodReference_Array {
    unMethodReference_Array :: ArrayType}
  deriving (Eq, Ord, Read, Show)

_MethodReference_Array = (Core.Name "hydra/langs/java/syntax.MethodReference.Array")

data ArrayCreationExpression = 
  ArrayCreationExpressionPrimitive ArrayCreationExpression_Primitive |
  ArrayCreationExpressionClassOrInterface ArrayCreationExpression_ClassOrInterface |
  ArrayCreationExpressionPrimitiveArray ArrayCreationExpression_PrimitiveArray |
  ArrayCreationExpressionClassOrInterfaceArray ArrayCreationExpression_ClassOrInterfaceArray
  deriving (Eq, Ord, Read, Show)

_ArrayCreationExpression = (Core.Name "hydra/langs/java/syntax.ArrayCreationExpression")

_ArrayCreationExpression_primitive = (Core.Name "primitive")

_ArrayCreationExpression_classOrInterface = (Core.Name "classOrInterface")

_ArrayCreationExpression_primitiveArray = (Core.Name "primitiveArray")

_ArrayCreationExpression_classOrInterfaceArray = (Core.Name "classOrInterfaceArray")

data ArrayCreationExpression_Primitive = 
  ArrayCreationExpression_Primitive {
    arrayCreationExpression_PrimitiveType :: PrimitiveTypeWithAnnotations,
    arrayCreationExpression_PrimitiveDimExprs :: [DimExpr],
    arrayCreationExpression_PrimitiveDims :: (Maybe Dims)}
  deriving (Eq, Ord, Read, Show)

_ArrayCreationExpression_Primitive = (Core.Name "hydra/langs/java/syntax.ArrayCreationExpression.Primitive")

_ArrayCreationExpression_Primitive_type = (Core.Name "type")

_ArrayCreationExpression_Primitive_dimExprs = (Core.Name "dimExprs")

_ArrayCreationExpression_Primitive_dims = (Core.Name "dims")

data ArrayCreationExpression_ClassOrInterface = 
  ArrayCreationExpression_ClassOrInterface {
    arrayCreationExpression_ClassOrInterfaceType :: ClassOrInterfaceType,
    arrayCreationExpression_ClassOrInterfaceDimExprs :: [DimExpr],
    arrayCreationExpression_ClassOrInterfaceDims :: (Maybe Dims)}
  deriving (Eq, Ord, Read, Show)

_ArrayCreationExpression_ClassOrInterface = (Core.Name "hydra/langs/java/syntax.ArrayCreationExpression.ClassOrInterface")

_ArrayCreationExpression_ClassOrInterface_type = (Core.Name "type")

_ArrayCreationExpression_ClassOrInterface_dimExprs = (Core.Name "dimExprs")

_ArrayCreationExpression_ClassOrInterface_dims = (Core.Name "dims")

data ArrayCreationExpression_PrimitiveArray = 
  ArrayCreationExpression_PrimitiveArray {
    arrayCreationExpression_PrimitiveArrayType :: PrimitiveTypeWithAnnotations,
    arrayCreationExpression_PrimitiveArrayDims :: [Dims],
    arrayCreationExpression_PrimitiveArrayArray :: ArrayInitializer}
  deriving (Eq, Ord, Read, Show)

_ArrayCreationExpression_PrimitiveArray = (Core.Name "hydra/langs/java/syntax.ArrayCreationExpression.PrimitiveArray")

_ArrayCreationExpression_PrimitiveArray_type = (Core.Name "type")

_ArrayCreationExpression_PrimitiveArray_dims = (Core.Name "dims")

_ArrayCreationExpression_PrimitiveArray_array = (Core.Name "array")

data ArrayCreationExpression_ClassOrInterfaceArray = 
  ArrayCreationExpression_ClassOrInterfaceArray {
    arrayCreationExpression_ClassOrInterfaceArrayType :: ClassOrInterfaceType,
    arrayCreationExpression_ClassOrInterfaceArrayDims :: [Dims],
    arrayCreationExpression_ClassOrInterfaceArrayArray :: ArrayInitializer}
  deriving (Eq, Ord, Read, Show)

_ArrayCreationExpression_ClassOrInterfaceArray = (Core.Name "hydra/langs/java/syntax.ArrayCreationExpression.ClassOrInterfaceArray")

_ArrayCreationExpression_ClassOrInterfaceArray_type = (Core.Name "type")

_ArrayCreationExpression_ClassOrInterfaceArray_dims = (Core.Name "dims")

_ArrayCreationExpression_ClassOrInterfaceArray_array = (Core.Name "array")

data DimExpr = 
  DimExpr {
    dimExprAnnotations :: [Annotation],
    dimExprExpression :: (Maybe Expression)}
  deriving (Eq, Ord, Read, Show)

_DimExpr = (Core.Name "hydra/langs/java/syntax.DimExpr")

_DimExpr_annotations = (Core.Name "annotations")

_DimExpr_expression = (Core.Name "expression")

data Expression = 
  ExpressionLambda LambdaExpression |
  ExpressionAssignment AssignmentExpression
  deriving (Eq, Ord, Read, Show)

_Expression = (Core.Name "hydra/langs/java/syntax.Expression")

_Expression_lambda = (Core.Name "lambda")

_Expression_assignment = (Core.Name "assignment")

data LambdaExpression = 
  LambdaExpression {
    lambdaExpressionParameters :: LambdaParameters,
    lambdaExpressionBody :: LambdaBody}
  deriving (Eq, Ord, Read, Show)

_LambdaExpression = (Core.Name "hydra/langs/java/syntax.LambdaExpression")

_LambdaExpression_parameters = (Core.Name "parameters")

_LambdaExpression_body = (Core.Name "body")

data LambdaParameters = 
  LambdaParametersTuple [LambdaParameters] |
  LambdaParametersSingle Identifier
  deriving (Eq, Ord, Read, Show)

_LambdaParameters = (Core.Name "hydra/langs/java/syntax.LambdaParameters")

_LambdaParameters_tuple = (Core.Name "tuple")

_LambdaParameters_single = (Core.Name "single")

data LambdaParameter = 
  LambdaParameterNormal LambdaParameter_Normal |
  LambdaParameterVariableArity VariableArityParameter
  deriving (Eq, Ord, Read, Show)

_LambdaParameter = (Core.Name "hydra/langs/java/syntax.LambdaParameter")

_LambdaParameter_normal = (Core.Name "normal")

_LambdaParameter_variableArity = (Core.Name "variableArity")

data LambdaParameter_Normal = 
  LambdaParameter_Normal {
    lambdaParameter_NormalModifiers :: [VariableModifier],
    lambdaParameter_NormalType :: LambdaParameterType,
    lambdaParameter_NormalId :: VariableDeclaratorId}
  deriving (Eq, Ord, Read, Show)

_LambdaParameter_Normal = (Core.Name "hydra/langs/java/syntax.LambdaParameter.Normal")

_LambdaParameter_Normal_modifiers = (Core.Name "modifiers")

_LambdaParameter_Normal_type = (Core.Name "type")

_LambdaParameter_Normal_id = (Core.Name "id")

data LambdaParameterType = 
  LambdaParameterTypeType UnannType |
  LambdaParameterTypeVar 
  deriving (Eq, Ord, Read, Show)

_LambdaParameterType = (Core.Name "hydra/langs/java/syntax.LambdaParameterType")

_LambdaParameterType_type = (Core.Name "type")

_LambdaParameterType_var = (Core.Name "var")

data LambdaBody = 
  LambdaBodyExpression Expression |
  LambdaBodyBlock Block
  deriving (Eq, Ord, Read, Show)

_LambdaBody = (Core.Name "hydra/langs/java/syntax.LambdaBody")

_LambdaBody_expression = (Core.Name "expression")

_LambdaBody_block = (Core.Name "block")

data AssignmentExpression = 
  AssignmentExpressionConditional ConditionalExpression |
  AssignmentExpressionAssignment Assignment
  deriving (Eq, Ord, Read, Show)

_AssignmentExpression = (Core.Name "hydra/langs/java/syntax.AssignmentExpression")

_AssignmentExpression_conditional = (Core.Name "conditional")

_AssignmentExpression_assignment = (Core.Name "assignment")

data Assignment = 
  Assignment {
    assignmentLhs :: LeftHandSide,
    assignmentOp :: AssignmentOperator,
    assignmentExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_Assignment = (Core.Name "hydra/langs/java/syntax.Assignment")

_Assignment_lhs = (Core.Name "lhs")

_Assignment_op = (Core.Name "op")

_Assignment_expression = (Core.Name "expression")

data LeftHandSide = 
  LeftHandSideExpressionName ExpressionName |
  LeftHandSideFieldAccess FieldAccess |
  LeftHandSideArrayAccess ArrayAccess
  deriving (Eq, Ord, Read, Show)

_LeftHandSide = (Core.Name "hydra/langs/java/syntax.LeftHandSide")

_LeftHandSide_expressionName = (Core.Name "expressionName")

_LeftHandSide_fieldAccess = (Core.Name "fieldAccess")

_LeftHandSide_arrayAccess = (Core.Name "arrayAccess")

data AssignmentOperator = 
  AssignmentOperatorSimple  |
  AssignmentOperatorTimes  |
  AssignmentOperatorDiv  |
  AssignmentOperatorMod  |
  AssignmentOperatorPlus  |
  AssignmentOperatorMinus  |
  AssignmentOperatorShiftLeft  |
  AssignmentOperatorShiftRight  |
  AssignmentOperatorShiftRightZeroFill  |
  AssignmentOperatorAnd  |
  AssignmentOperatorXor  |
  AssignmentOperatorOr 
  deriving (Eq, Ord, Read, Show)

_AssignmentOperator = (Core.Name "hydra/langs/java/syntax.AssignmentOperator")

_AssignmentOperator_simple = (Core.Name "simple")

_AssignmentOperator_times = (Core.Name "times")

_AssignmentOperator_div = (Core.Name "div")

_AssignmentOperator_mod = (Core.Name "mod")

_AssignmentOperator_plus = (Core.Name "plus")

_AssignmentOperator_minus = (Core.Name "minus")

_AssignmentOperator_shiftLeft = (Core.Name "shiftLeft")

_AssignmentOperator_shiftRight = (Core.Name "shiftRight")

_AssignmentOperator_shiftRightZeroFill = (Core.Name "shiftRightZeroFill")

_AssignmentOperator_and = (Core.Name "and")

_AssignmentOperator_xor = (Core.Name "xor")

_AssignmentOperator_or = (Core.Name "or")

data ConditionalExpression = 
  ConditionalExpressionSimple ConditionalOrExpression |
  ConditionalExpressionTernaryCond ConditionalExpression_TernaryCond |
  ConditionalExpressionTernaryLambda ConditionalExpression_TernaryLambda
  deriving (Eq, Ord, Read, Show)

_ConditionalExpression = (Core.Name "hydra/langs/java/syntax.ConditionalExpression")

_ConditionalExpression_simple = (Core.Name "simple")

_ConditionalExpression_ternaryCond = (Core.Name "ternaryCond")

_ConditionalExpression_ternaryLambda = (Core.Name "ternaryLambda")

data ConditionalExpression_TernaryCond = 
  ConditionalExpression_TernaryCond {
    conditionalExpression_TernaryCondCond :: ConditionalOrExpression,
    conditionalExpression_TernaryCondIfTrue :: Expression,
    conditionalExpression_TernaryCondIfFalse :: ConditionalExpression}
  deriving (Eq, Ord, Read, Show)

_ConditionalExpression_TernaryCond = (Core.Name "hydra/langs/java/syntax.ConditionalExpression.TernaryCond")

_ConditionalExpression_TernaryCond_cond = (Core.Name "cond")

_ConditionalExpression_TernaryCond_ifTrue = (Core.Name "ifTrue")

_ConditionalExpression_TernaryCond_ifFalse = (Core.Name "ifFalse")

data ConditionalExpression_TernaryLambda = 
  ConditionalExpression_TernaryLambda {
    conditionalExpression_TernaryLambdaCond :: ConditionalOrExpression,
    conditionalExpression_TernaryLambdaIfTrue :: Expression,
    conditionalExpression_TernaryLambdaIfFalse :: LambdaExpression}
  deriving (Eq, Ord, Read, Show)

_ConditionalExpression_TernaryLambda = (Core.Name "hydra/langs/java/syntax.ConditionalExpression.TernaryLambda")

_ConditionalExpression_TernaryLambda_cond = (Core.Name "cond")

_ConditionalExpression_TernaryLambda_ifTrue = (Core.Name "ifTrue")

_ConditionalExpression_TernaryLambda_ifFalse = (Core.Name "ifFalse")

newtype ConditionalOrExpression = 
  ConditionalOrExpression {
    unConditionalOrExpression :: [ConditionalAndExpression]}
  deriving (Eq, Ord, Read, Show)

_ConditionalOrExpression = (Core.Name "hydra/langs/java/syntax.ConditionalOrExpression")

newtype ConditionalAndExpression = 
  ConditionalAndExpression {
    unConditionalAndExpression :: [InclusiveOrExpression]}
  deriving (Eq, Ord, Read, Show)

_ConditionalAndExpression = (Core.Name "hydra/langs/java/syntax.ConditionalAndExpression")

newtype InclusiveOrExpression = 
  InclusiveOrExpression {
    unInclusiveOrExpression :: [ExclusiveOrExpression]}
  deriving (Eq, Ord, Read, Show)

_InclusiveOrExpression = (Core.Name "hydra/langs/java/syntax.InclusiveOrExpression")

newtype ExclusiveOrExpression = 
  ExclusiveOrExpression {
    unExclusiveOrExpression :: [AndExpression]}
  deriving (Eq, Ord, Read, Show)

_ExclusiveOrExpression = (Core.Name "hydra/langs/java/syntax.ExclusiveOrExpression")

newtype AndExpression = 
  AndExpression {
    unAndExpression :: [EqualityExpression]}
  deriving (Eq, Ord, Read, Show)

_AndExpression = (Core.Name "hydra/langs/java/syntax.AndExpression")

data EqualityExpression = 
  EqualityExpressionUnary RelationalExpression |
  EqualityExpressionEqual EqualityExpression_Binary |
  EqualityExpressionNotEqual EqualityExpression_Binary
  deriving (Eq, Ord, Read, Show)

_EqualityExpression = (Core.Name "hydra/langs/java/syntax.EqualityExpression")

_EqualityExpression_unary = (Core.Name "unary")

_EqualityExpression_equal = (Core.Name "equal")

_EqualityExpression_notEqual = (Core.Name "notEqual")

data EqualityExpression_Binary = 
  EqualityExpression_Binary {
    equalityExpression_BinaryLhs :: EqualityExpression,
    equalityExpression_BinaryRhs :: RelationalExpression}
  deriving (Eq, Ord, Read, Show)

_EqualityExpression_Binary = (Core.Name "hydra/langs/java/syntax.EqualityExpression.Binary")

_EqualityExpression_Binary_lhs = (Core.Name "lhs")

_EqualityExpression_Binary_rhs = (Core.Name "rhs")

data RelationalExpression = 
  RelationalExpressionSimple ShiftExpression |
  RelationalExpressionLessThan RelationalExpression_LessThan |
  RelationalExpressionGreaterThan RelationalExpression_GreaterThan |
  RelationalExpressionLessThanEqual RelationalExpression_LessThanEqual |
  RelationalExpressionGreaterThanEqual RelationalExpression_GreaterThanEqual |
  RelationalExpressionInstanceof RelationalExpression_InstanceOf
  deriving (Eq, Ord, Read, Show)

_RelationalExpression = (Core.Name "hydra/langs/java/syntax.RelationalExpression")

_RelationalExpression_simple = (Core.Name "simple")

_RelationalExpression_lessThan = (Core.Name "lessThan")

_RelationalExpression_greaterThan = (Core.Name "greaterThan")

_RelationalExpression_lessThanEqual = (Core.Name "lessThanEqual")

_RelationalExpression_greaterThanEqual = (Core.Name "greaterThanEqual")

_RelationalExpression_instanceof = (Core.Name "instanceof")

data RelationalExpression_LessThan = 
  RelationalExpression_LessThan {
    relationalExpression_LessThanLhs :: RelationalExpression,
    relationalExpression_LessThanRhs :: ShiftExpression}
  deriving (Eq, Ord, Read, Show)

_RelationalExpression_LessThan = (Core.Name "hydra/langs/java/syntax.RelationalExpression.LessThan")

_RelationalExpression_LessThan_lhs = (Core.Name "lhs")

_RelationalExpression_LessThan_rhs = (Core.Name "rhs")

data RelationalExpression_GreaterThan = 
  RelationalExpression_GreaterThan {
    relationalExpression_GreaterThanLhs :: RelationalExpression,
    relationalExpression_GreaterThanRhs :: ShiftExpression}
  deriving (Eq, Ord, Read, Show)

_RelationalExpression_GreaterThan = (Core.Name "hydra/langs/java/syntax.RelationalExpression.GreaterThan")

_RelationalExpression_GreaterThan_lhs = (Core.Name "lhs")

_RelationalExpression_GreaterThan_rhs = (Core.Name "rhs")

data RelationalExpression_LessThanEqual = 
  RelationalExpression_LessThanEqual {
    relationalExpression_LessThanEqualLhs :: RelationalExpression,
    relationalExpression_LessThanEqualRhs :: ShiftExpression}
  deriving (Eq, Ord, Read, Show)

_RelationalExpression_LessThanEqual = (Core.Name "hydra/langs/java/syntax.RelationalExpression.LessThanEqual")

_RelationalExpression_LessThanEqual_lhs = (Core.Name "lhs")

_RelationalExpression_LessThanEqual_rhs = (Core.Name "rhs")

data RelationalExpression_GreaterThanEqual = 
  RelationalExpression_GreaterThanEqual {
    relationalExpression_GreaterThanEqualLhs :: RelationalExpression,
    relationalExpression_GreaterThanEqualRhs :: ShiftExpression}
  deriving (Eq, Ord, Read, Show)

_RelationalExpression_GreaterThanEqual = (Core.Name "hydra/langs/java/syntax.RelationalExpression.GreaterThanEqual")

_RelationalExpression_GreaterThanEqual_lhs = (Core.Name "lhs")

_RelationalExpression_GreaterThanEqual_rhs = (Core.Name "rhs")

data RelationalExpression_InstanceOf = 
  RelationalExpression_InstanceOf {
    relationalExpression_InstanceOfLhs :: RelationalExpression,
    relationalExpression_InstanceOfRhs :: ReferenceType}
  deriving (Eq, Ord, Read, Show)

_RelationalExpression_InstanceOf = (Core.Name "hydra/langs/java/syntax.RelationalExpression.InstanceOf")

_RelationalExpression_InstanceOf_lhs = (Core.Name "lhs")

_RelationalExpression_InstanceOf_rhs = (Core.Name "rhs")

data ShiftExpression = 
  ShiftExpressionUnary AdditiveExpression |
  ShiftExpressionShiftLeft ShiftExpression_Binary |
  ShiftExpressionShiftRight ShiftExpression_Binary |
  ShiftExpressionShiftRightZeroFill ShiftExpression_Binary
  deriving (Eq, Ord, Read, Show)

_ShiftExpression = (Core.Name "hydra/langs/java/syntax.ShiftExpression")

_ShiftExpression_unary = (Core.Name "unary")

_ShiftExpression_shiftLeft = (Core.Name "shiftLeft")

_ShiftExpression_shiftRight = (Core.Name "shiftRight")

_ShiftExpression_shiftRightZeroFill = (Core.Name "shiftRightZeroFill")

data ShiftExpression_Binary = 
  ShiftExpression_Binary {
    shiftExpression_BinaryLhs :: ShiftExpression,
    shiftExpression_BinaryRhs :: AdditiveExpression}
  deriving (Eq, Ord, Read, Show)

_ShiftExpression_Binary = (Core.Name "hydra/langs/java/syntax.ShiftExpression.Binary")

_ShiftExpression_Binary_lhs = (Core.Name "lhs")

_ShiftExpression_Binary_rhs = (Core.Name "rhs")

data AdditiveExpression = 
  AdditiveExpressionUnary MultiplicativeExpression |
  AdditiveExpressionPlus AdditiveExpression_Binary |
  AdditiveExpressionMinus AdditiveExpression_Binary
  deriving (Eq, Ord, Read, Show)

_AdditiveExpression = (Core.Name "hydra/langs/java/syntax.AdditiveExpression")

_AdditiveExpression_unary = (Core.Name "unary")

_AdditiveExpression_plus = (Core.Name "plus")

_AdditiveExpression_minus = (Core.Name "minus")

data AdditiveExpression_Binary = 
  AdditiveExpression_Binary {
    additiveExpression_BinaryLhs :: AdditiveExpression,
    additiveExpression_BinaryRhs :: MultiplicativeExpression}
  deriving (Eq, Ord, Read, Show)

_AdditiveExpression_Binary = (Core.Name "hydra/langs/java/syntax.AdditiveExpression.Binary")

_AdditiveExpression_Binary_lhs = (Core.Name "lhs")

_AdditiveExpression_Binary_rhs = (Core.Name "rhs")

data MultiplicativeExpression = 
  MultiplicativeExpressionUnary UnaryExpression |
  MultiplicativeExpressionTimes MultiplicativeExpression_Binary |
  MultiplicativeExpressionDivide MultiplicativeExpression_Binary |
  MultiplicativeExpressionMod MultiplicativeExpression_Binary
  deriving (Eq, Ord, Read, Show)

_MultiplicativeExpression = (Core.Name "hydra/langs/java/syntax.MultiplicativeExpression")

_MultiplicativeExpression_unary = (Core.Name "unary")

_MultiplicativeExpression_times = (Core.Name "times")

_MultiplicativeExpression_divide = (Core.Name "divide")

_MultiplicativeExpression_mod = (Core.Name "mod")

data MultiplicativeExpression_Binary = 
  MultiplicativeExpression_Binary {
    multiplicativeExpression_BinaryLhs :: MultiplicativeExpression,
    multiplicativeExpression_BinaryRhs :: UnaryExpression}
  deriving (Eq, Ord, Read, Show)

_MultiplicativeExpression_Binary = (Core.Name "hydra/langs/java/syntax.MultiplicativeExpression.Binary")

_MultiplicativeExpression_Binary_lhs = (Core.Name "lhs")

_MultiplicativeExpression_Binary_rhs = (Core.Name "rhs")

data UnaryExpression = 
  UnaryExpressionPreIncrement PreIncrementExpression |
  UnaryExpressionPreDecrement PreDecrementExpression |
  UnaryExpressionPlus UnaryExpression |
  UnaryExpressionMinus UnaryExpression |
  UnaryExpressionOther UnaryExpressionNotPlusMinus
  deriving (Eq, Ord, Read, Show)

_UnaryExpression = (Core.Name "hydra/langs/java/syntax.UnaryExpression")

_UnaryExpression_preIncrement = (Core.Name "preIncrement")

_UnaryExpression_preDecrement = (Core.Name "preDecrement")

_UnaryExpression_plus = (Core.Name "plus")

_UnaryExpression_minus = (Core.Name "minus")

_UnaryExpression_other = (Core.Name "other")

newtype PreIncrementExpression = 
  PreIncrementExpression {
    unPreIncrementExpression :: UnaryExpression}
  deriving (Eq, Ord, Read, Show)

_PreIncrementExpression = (Core.Name "hydra/langs/java/syntax.PreIncrementExpression")

newtype PreDecrementExpression = 
  PreDecrementExpression {
    unPreDecrementExpression :: UnaryExpression}
  deriving (Eq, Ord, Read, Show)

_PreDecrementExpression = (Core.Name "hydra/langs/java/syntax.PreDecrementExpression")

data UnaryExpressionNotPlusMinus = 
  UnaryExpressionNotPlusMinusPostfix PostfixExpression |
  UnaryExpressionNotPlusMinusTilde UnaryExpression |
  UnaryExpressionNotPlusMinusNot UnaryExpression |
  UnaryExpressionNotPlusMinusCast CastExpression
  deriving (Eq, Ord, Read, Show)

_UnaryExpressionNotPlusMinus = (Core.Name "hydra/langs/java/syntax.UnaryExpressionNotPlusMinus")

_UnaryExpressionNotPlusMinus_postfix = (Core.Name "postfix")

_UnaryExpressionNotPlusMinus_tilde = (Core.Name "tilde")

_UnaryExpressionNotPlusMinus_not = (Core.Name "not")

_UnaryExpressionNotPlusMinus_cast = (Core.Name "cast")

data PostfixExpression = 
  PostfixExpressionPrimary Primary |
  PostfixExpressionName ExpressionName |
  PostfixExpressionPostIncrement PostIncrementExpression |
  PostfixExpressionPostDecrement PostDecrementExpression
  deriving (Eq, Ord, Read, Show)

_PostfixExpression = (Core.Name "hydra/langs/java/syntax.PostfixExpression")

_PostfixExpression_primary = (Core.Name "primary")

_PostfixExpression_name = (Core.Name "name")

_PostfixExpression_postIncrement = (Core.Name "postIncrement")

_PostfixExpression_postDecrement = (Core.Name "postDecrement")

newtype PostIncrementExpression = 
  PostIncrementExpression {
    unPostIncrementExpression :: PostfixExpression}
  deriving (Eq, Ord, Read, Show)

_PostIncrementExpression = (Core.Name "hydra/langs/java/syntax.PostIncrementExpression")

newtype PostDecrementExpression = 
  PostDecrementExpression {
    unPostDecrementExpression :: PostfixExpression}
  deriving (Eq, Ord, Read, Show)

_PostDecrementExpression = (Core.Name "hydra/langs/java/syntax.PostDecrementExpression")

data CastExpression = 
  CastExpressionPrimitive CastExpression_Primitive |
  CastExpressionNotPlusMinus CastExpression_NotPlusMinus |
  CastExpressionLambda CastExpression_Lambda
  deriving (Eq, Ord, Read, Show)

_CastExpression = (Core.Name "hydra/langs/java/syntax.CastExpression")

_CastExpression_primitive = (Core.Name "primitive")

_CastExpression_notPlusMinus = (Core.Name "notPlusMinus")

_CastExpression_lambda = (Core.Name "lambda")

data CastExpression_Primitive = 
  CastExpression_Primitive {
    castExpression_PrimitiveType :: PrimitiveTypeWithAnnotations,
    castExpression_PrimitiveExpression :: UnaryExpression}
  deriving (Eq, Ord, Read, Show)

_CastExpression_Primitive = (Core.Name "hydra/langs/java/syntax.CastExpression.Primitive")

_CastExpression_Primitive_type = (Core.Name "type")

_CastExpression_Primitive_expression = (Core.Name "expression")

data CastExpression_NotPlusMinus = 
  CastExpression_NotPlusMinus {
    castExpression_NotPlusMinusRefAndBounds :: CastExpression_RefAndBounds,
    castExpression_NotPlusMinusExpression :: UnaryExpression}
  deriving (Eq, Ord, Read, Show)

_CastExpression_NotPlusMinus = (Core.Name "hydra/langs/java/syntax.CastExpression.NotPlusMinus")

_CastExpression_NotPlusMinus_refAndBounds = (Core.Name "refAndBounds")

_CastExpression_NotPlusMinus_expression = (Core.Name "expression")

data CastExpression_Lambda = 
  CastExpression_Lambda {
    castExpression_LambdaRefAndBounds :: CastExpression_RefAndBounds,
    castExpression_LambdaExpression :: LambdaExpression}
  deriving (Eq, Ord, Read, Show)

_CastExpression_Lambda = (Core.Name "hydra/langs/java/syntax.CastExpression.Lambda")

_CastExpression_Lambda_refAndBounds = (Core.Name "refAndBounds")

_CastExpression_Lambda_expression = (Core.Name "expression")

data CastExpression_RefAndBounds = 
  CastExpression_RefAndBounds {
    castExpression_RefAndBoundsType :: ReferenceType,
    castExpression_RefAndBoundsBounds :: [AdditionalBound]}
  deriving (Eq, Ord, Read, Show)

_CastExpression_RefAndBounds = (Core.Name "hydra/langs/java/syntax.CastExpression.RefAndBounds")

_CastExpression_RefAndBounds_type = (Core.Name "type")

_CastExpression_RefAndBounds_bounds = (Core.Name "bounds")

newtype ConstantExpression = 
  ConstantExpression {
    unConstantExpression :: Expression}
  deriving (Eq, Ord, Read, Show)

_ConstantExpression = (Core.Name "hydra/langs/java/syntax.ConstantExpression")
