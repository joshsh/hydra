{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier2.Basics where

-- Standard Tier-2 imports
import           Prelude hiding ((++))
import qualified Data.List                 as L
import qualified Data.Map                  as M
import qualified Data.Set                  as S
import qualified Data.Maybe                as Y
import           Hydra.Dsl.Base            as Base
import qualified Hydra.Dsl.Core            as Core
import qualified Hydra.Dsl.Graph           as Graph
import qualified Hydra.Dsl.Lib.Equality    as Equality
import qualified Hydra.Dsl.Lib.Flows       as Flows
import qualified Hydra.Dsl.Lib.Io          as Io
import qualified Hydra.Dsl.Lib.Lists       as Lists
import qualified Hydra.Dsl.Lib.Literals    as Literals
import qualified Hydra.Dsl.Lib.Logic       as Logic
import qualified Hydra.Dsl.Lib.Maps        as Maps
import qualified Hydra.Dsl.Lib.Math        as Math
import qualified Hydra.Dsl.Lib.Optionals   as Optionals
import qualified Hydra.Dsl.Lib.Sets        as Sets
import           Hydra.Dsl.Lib.Strings     as Strings
import qualified Hydra.Dsl.Module          as Module
import qualified Hydra.Dsl.Terms           as Terms
import qualified Hydra.Dsl.Types           as Types
import           Hydra.Sources.Tier1.All


basicsDefinition :: String -> Datum a -> Definition a
basicsDefinition = definitionInModule hydraBasicsModule

hydraBasicsModule :: Module Kv
hydraBasicsModule = Module (Namespace "hydra/basics") elements [hydraTier1Module] $
    Just "A tier-2 module of basic functions for working with types and terms."
  where
   elements = [
     el eliminationVariantDef,
     el eliminationVariantsDef,
     el floatTypePrecisionDef,
     el floatTypesDef,
     el floatValueTypeDef,
     el functionVariantDef,
     el functionVariantsDef,
     el idDef,
     el integerTypeIsSignedDef,
     el integerTypePrecisionDef,
     el integerTypesDef,
     el integerValueTypeDef,
     el literalTypeDef,
     el literalTypeVariantDef,
     el literalVariantDef,
     el literalVariantsDef,
     el termMetaDef,
     el termVariantDef,
     el termVariantsDef,
     el typeVariantDef,
     el typeVariantsDef,
     -- Formatting.hs
     el capitalizeDef,
     el decapitalizeDef,
     el mapFirstLetterDef,
     -- Common.hs
     el fieldMapDef,
     el fieldTypeMapDef,
     el isEncodedTypeDef,
     el isTypeDef,
     el isUnitTermDef,
     el isUnitTypeDef,
     el elementsToGraphDef,
     el localNameOfEagerDef,
     el localNameOfLazyDef,
     el namespaceOfEagerDef,
     el namespaceOfLazyDef,
     el namespaceToFilePathDef,
     el qualifyNameEagerDef,
     el qualifyNameLazyDef
     ]

eliminationVariantDef :: Definition (Elimination a -> EliminationVariant)
eliminationVariantDef = basicsDefinition "eliminationVariant" $
  doc "Find the elimination variant (constructor) for a given elimination term" $
  typed (functionT (Types.apply (TypeVariable _Elimination) (Types.var "a")) (TypeVariable _EliminationVariant)) $
  matchToEnum _Elimination _EliminationVariant Nothing [
    _Elimination_list     @-> _EliminationVariant_list,
    _Elimination_optional @-> _EliminationVariant_optional,
    _Elimination_product  @-> _EliminationVariant_product,
    _Elimination_record   @-> _EliminationVariant_record,
    _Elimination_union    @-> _EliminationVariant_union,
    _Elimination_wrap     @-> _EliminationVariant_wrap]

eliminationVariantsDef :: Definition [EliminationVariant]
eliminationVariantsDef = basicsDefinition "eliminationVariants" $
  doc "All elimination variants (constructors), in a canonical order" $
  list $ unitVariant _EliminationVariant <$> [
    _EliminationVariant_list,
    _EliminationVariant_wrap,
    _EliminationVariant_optional,
    _EliminationVariant_product,
    _EliminationVariant_record,
    _EliminationVariant_union]

floatTypePrecisionDef :: Definition (FloatType -> Precision)
floatTypePrecisionDef = basicsDefinition "floatTypePrecision" $
  doc "Find the precision of a given floating-point type" $
  matchToUnion _FloatType _Precision Nothing [
    _FloatType_bigfloat @-> field _Precision_arbitrary unit,
    _FloatType_float32  @-> field _Precision_bits $ int 32,
    _FloatType_float64  @-> field _Precision_bits $ int 64]

floatTypesDef :: Definition [FloatType]
floatTypesDef = basicsDefinition "floatTypes" $
  doc "All floating-point types in a canonical order" $
  list $ unitVariant _FloatType <$> [
    _FloatType_bigfloat,
    _FloatType_float32,
    _FloatType_float64]

floatValueTypeDef :: Definition (FloatValue -> FloatType)
floatValueTypeDef = basicsDefinition "floatValueType" $
  doc "Find the float type for a given floating-point value" $
  matchToEnum _FloatValue _FloatType Nothing [
    _FloatValue_bigfloat @-> _FloatType_bigfloat,
    _FloatValue_float32  @-> _FloatType_float32,
    _FloatValue_float64  @-> _FloatType_float64]

functionVariantDef :: Definition (Function a -> FunctionVariant)
functionVariantDef = basicsDefinition "functionVariant" $
  doc "Find the function variant (constructor) for a given function" $
  typed (functionT (Types.apply (TypeVariable _Function) (Types.var "a")) (TypeVariable _FunctionVariant)) $
  matchToEnum _Function _FunctionVariant Nothing [
    _Function_elimination @-> _FunctionVariant_elimination,
    _Function_lambda      @-> _FunctionVariant_lambda,
    _Function_primitive   @-> _FunctionVariant_primitive]

functionVariantsDef :: Definition [FunctionVariant]
functionVariantsDef = basicsDefinition "functionVariants" $
  doc "All function variants (constructors), in a canonical order" $
  list $ unitVariant _FunctionVariant <$> [
    _FunctionVariant_elimination,
    _FunctionVariant_lambda,
    _FunctionVariant_primitive]

idDef :: Definition (a -> a)
idDef = basicsDefinition "id" $
  doc "The identity function" $
  typed (functionT (Types.var "a") (Types.var "a")) $
  lambda "x" $ var "x"

integerTypeIsSignedDef :: Definition (IntegerType -> Bool)
integerTypeIsSignedDef = basicsDefinition "integerTypeIsSigned" $
  doc "Find whether a given integer type is signed (true) or unsigned (false)" $
  matchData _IntegerType Nothing [
    _IntegerType_bigint @-> constant true,
    _IntegerType_int8   @-> constant true,
    _IntegerType_int16  @-> constant true,
    _IntegerType_int32  @-> constant true,
    _IntegerType_int64  @-> constant true,
    _IntegerType_uint8  @-> constant false,
    _IntegerType_uint16 @-> constant false,
    _IntegerType_uint32 @-> constant false,
    _IntegerType_uint64 @-> constant false]

integerTypePrecisionDef :: Definition (IntegerType -> Precision)
integerTypePrecisionDef = basicsDefinition "integerTypePrecision" $
  doc "Find the precision of a given integer type" $
  matchToUnion _IntegerType _Precision Nothing [
    _IntegerType_bigint @-> field _Precision_arbitrary unit,
    _IntegerType_int8   @-> field _Precision_bits $ int 8,
    _IntegerType_int16  @-> field _Precision_bits $ int 16,
    _IntegerType_int32  @-> field _Precision_bits $ int 32,
    _IntegerType_int64  @-> field _Precision_bits $ int 64,
    _IntegerType_uint8  @-> field _Precision_bits $ int 8,
    _IntegerType_uint16 @-> field _Precision_bits $ int 16,
    _IntegerType_uint32 @-> field _Precision_bits $ int 32,
    _IntegerType_uint64 @-> field _Precision_bits $ int 64]

integerTypesDef :: Definition [IntegerType]
integerTypesDef = basicsDefinition "integerTypes" $
    doc "All integer types, in a canonical order" $
    list $ unitVariant _IntegerType <$> [
      _IntegerType_bigint,
      _IntegerType_int8,
      _IntegerType_int16,
      _IntegerType_int32,
      _IntegerType_int64,
      _IntegerType_uint8,
      _IntegerType_uint16,
      _IntegerType_uint32,
      _IntegerType_uint64]

integerValueTypeDef :: Definition (IntegerValue -> IntegerType)
integerValueTypeDef = basicsDefinition "integerValueType" $
  doc "Find the integer type for a given integer value" $
  matchToEnum _IntegerValue _IntegerType Nothing [
    _IntegerValue_bigint @-> _IntegerType_bigint,
    _IntegerValue_int8   @-> _IntegerType_int8,
    _IntegerValue_int16  @-> _IntegerType_int16,
    _IntegerValue_int32  @-> _IntegerType_int32,
    _IntegerValue_int64  @-> _IntegerType_int64,
    _IntegerValue_uint8  @-> _IntegerType_uint8,
    _IntegerValue_uint16 @-> _IntegerType_uint16,
    _IntegerValue_uint32 @-> _IntegerType_uint32,
    _IntegerValue_uint64 @-> _IntegerType_uint64]

literalTypeDef :: Definition (Literal -> LiteralType)
literalTypeDef = basicsDefinition "literalType" $
  doc "Find the literal type for a given literal value" $
  match _Literal Nothing [
    Case _Literal_binary  --> constant $ variant _LiteralType _LiteralType_binary unit,
    Case _Literal_boolean --> constant $ variant _LiteralType _LiteralType_boolean unit,
    Case _Literal_float   --> inject2 _LiteralType _LiteralType_float <.> ref floatValueTypeDef,
    Case _Literal_integer --> inject2 _LiteralType _LiteralType_integer <.> ref integerValueTypeDef,
    Case _Literal_string  --> constant $ variant _LiteralType _LiteralType_string unit]

literalTypeVariantDef :: Definition (LiteralType -> LiteralVariant)
literalTypeVariantDef = basicsDefinition "literalTypeVariant" $
  doc "Find the literal type variant (constructor) for a given literal value" $
  matchToEnum _LiteralType _LiteralVariant Nothing [
    _LiteralType_binary  @-> _LiteralVariant_binary,
    _LiteralType_boolean @-> _LiteralVariant_boolean,
    _LiteralType_float   @-> _LiteralVariant_float,
    _LiteralType_integer @-> _LiteralVariant_integer,
    _LiteralType_string  @-> _LiteralVariant_string]

literalVariantDef :: Definition (Literal -> LiteralVariant)
literalVariantDef = basicsDefinition "literalVariant" $
  doc "Find the literal variant (constructor) for a given literal value" $
  function (TypeVariable _Literal) (TypeVariable _LiteralVariant) $
  ref literalTypeVariantDef <.> ref literalTypeDef

literalVariantsDef :: Definition [LiteralVariant]
literalVariantsDef = basicsDefinition "literalVariants" $
  doc "All literal variants, in a canonical order" $
  list $ unitVariant _LiteralVariant <$> [
    _LiteralVariant_binary,
    _LiteralVariant_boolean,
    _LiteralVariant_float,
    _LiteralVariant_integer,
    _LiteralVariant_string]

termMetaDef :: Definition (Graph a -> Term a -> a)
termMetaDef = basicsDefinition "termMeta" $
  function graphA (functionT termA aT) $
  (project _AnnotationClass _AnnotationClass_termAnnotation) <.> Graph.graphAnnotations

termVariantDef :: Definition (Term a -> TermVariant)
termVariantDef = basicsDefinition "termVariant" $
  doc "Find the term variant (constructor) for a given term" $
  function termA (TypeVariable _TermVariant) $
    matchToEnum _Term _TermVariant Nothing [
      _Term_annotated   @-> _TermVariant_annotated,
      _Term_application @-> _TermVariant_application,
      _Term_function    @-> _TermVariant_function,
      _Term_let         @-> _TermVariant_let,
      _Term_list        @-> _TermVariant_list,
      _Term_literal     @-> _TermVariant_literal,
      _Term_map         @-> _TermVariant_map,
      _Term_optional    @-> _TermVariant_optional,
      _Term_product     @-> _TermVariant_product,
      _Term_record      @-> _TermVariant_record,
      _Term_set         @-> _TermVariant_set,
      _Term_stream      @-> _TermVariant_stream,
      _Term_sum         @-> _TermVariant_sum,
      _Term_union       @-> _TermVariant_union,
      _Term_variable    @-> _TermVariant_variable,
      _Term_wrap        @-> _TermVariant_wrap]

termVariantsDef :: Definition [TermVariant]
termVariantsDef = basicsDefinition "termVariants" $
  doc "All term (expression) variants, in a canonical order" $
  list $ unitVariant _TermVariant <$> [
    _TermVariant_annotated,
    _TermVariant_application,
    _TermVariant_literal,
    _TermVariant_function,
    _TermVariant_list,
    _TermVariant_map,
    _TermVariant_optional,
    _TermVariant_product,
    _TermVariant_record,
    _TermVariant_set,
    _TermVariant_stream,
    _TermVariant_sum,
    _TermVariant_union,
    _TermVariant_variable,
    _TermVariant_wrap]

typeVariantDef :: Definition (Type a -> TypeVariant)
typeVariantDef = basicsDefinition "typeVariant" $
  doc "Find the type variant (constructor) for a given type" $
  function typeA (TypeVariable _TypeVariant) $
    matchToEnum _Type _TypeVariant Nothing [
      _Type_annotated   @-> _TypeVariant_annotated,
      _Type_application @-> _TypeVariant_application,
      _Type_function    @-> _TypeVariant_function,
      _Type_lambda      @-> _TypeVariant_lambda,
      _Type_list        @-> _TypeVariant_list,
      _Type_literal     @-> _TypeVariant_literal,
      _Type_map         @-> _TypeVariant_map,
      _Type_optional    @-> _TypeVariant_optional,
      _Type_product     @-> _TypeVariant_product,
      _Type_record      @-> _TypeVariant_record,
      _Type_set         @-> _TypeVariant_set,
      _Type_stream      @-> _TypeVariant_stream,
      _Type_sum         @-> _TypeVariant_sum,
      _Type_union       @-> _TypeVariant_union,
      _Type_variable    @-> _TypeVariant_variable,
      _Type_wrap        @-> _TypeVariant_wrap]

typeVariantsDef :: Definition [TypeVariant]
typeVariantsDef = basicsDefinition "typeVariants" $
  doc "All type variants, in a canonical order" $
  list $ unitVariant _TypeVariant <$> [
    _TypeVariant_annotated,
    _TypeVariant_application,
    _TypeVariant_function,
    _TypeVariant_lambda,
    _TypeVariant_list,
    _TypeVariant_literal,
    _TypeVariant_map,
    _TypeVariant_wrap,
    _TypeVariant_optional,
    _TypeVariant_product,
    _TypeVariant_record,
    _TypeVariant_set,
    _TypeVariant_stream,
    _TypeVariant_sum,
    _TypeVariant_union,
    _TypeVariant_variable]

-- Formatting.hs

capitalizeDef :: Definition (String -> String)
capitalizeDef = basicsDefinition "capitalize" $
  doc "Capitalize the first letter of a string" $
  function Types.string Types.string $
  ref mapFirstLetterDef @@ Strings.toUpper

decapitalizeDef :: Definition (String -> String)
decapitalizeDef = basicsDefinition "decapitalize" $
  doc "Decapitalize the first letter of a string" $
  function Types.string Types.string $
  ref mapFirstLetterDef @@ Strings.toLower

-- TODO: simplify this helper
mapFirstLetterDef :: Definition ((String -> String) -> String -> String)
mapFirstLetterDef = basicsDefinition "mapFirstLetter" $
  doc "A helper which maps the first letter of a string to another string" $
  lambda "mapping" $ lambda "s" ((Logic.ifElse
       @@ var "s"
       @@ (Strings.cat2 @@ var "firstLetter" @@ (Strings.fromList @@ (Lists.tail @@ var "list")))
       @@ (Strings.isEmpty @@ var "s"))
    `with` [
      "firstLetter">: var "mapping" @@ (Strings.fromList @@ (Lists.pure @@ (Lists.head @@ var "list"))),
      "list">: typed (TypeList $ Types.int32) $ Strings.toList @@ var "s"])

-- Common.hs

fieldMapDef :: Definition ([Field a] -> M.Map FieldName (Term a))
fieldMapDef = basicsDefinition "fieldMap" $
  function (TypeList fieldA) (Types.map (TypeVariable _FieldName) termA) $
    (lambda "fields" $ Maps.fromList @@ (Lists.map @@ var "toPair" @@ var "fields"))
  `with` [
    "toPair">: lambda "f" $ pair (project _Field _Field_name @@ var "f") (project _Field _Field_term @@ var "f")]

fieldTypeMapDef :: Definition ([FieldType a] -> M.Map FieldName (Type a))
fieldTypeMapDef = basicsDefinition "fieldTypeMap" $
  function (TypeList fieldTypeA) (Types.map (TypeVariable _FieldName) typeA) $
    (lambda "fields" $ Maps.fromList @@ (Lists.map @@ var "toPair" @@ var "fields"))
  `with` [
    "toPair">: lambda "f" $ pair (project _FieldType _FieldType_name @@ var "f") (project _FieldType _FieldType_type @@ var "f")]

isEncodedTypeDef :: Definition (Term a -> Bool)
isEncodedTypeDef = basicsDefinition "isEncodedType" $
  function termA booleanT $
  lambda "t" $ (match _Term (Just false) [
      Case _Term_application --> lambda "a" $
        ref isEncodedTypeDef @@ (project _Application _Application_function @@ var "a"),
      Case _Term_union       --> lambda "i" $
        Equality.equalString @@ (string $ unName _Type) @@ (unwrap _Name @@ (project _Injection _Injection_typeName @@ var "i"))
    ]) @@ (ref stripTermDef @@ var "t")

isTypeDef :: Definition (Type a -> Bool)
isTypeDef = basicsDefinition "isType" $
  functionWithClasses typeA booleanT eqA $
  lambda "t" $ (match _Type (Just false) [
      Case _Type_application --> lambda "a" $
        ref isTypeDef @@ (project _ApplicationType _ApplicationType_function @@ var "a"),
      Case _Type_lambda --> lambda "l" $
        ref isTypeDef @@ (project _LambdaType _LambdaType_body @@ var "l"),
      Case _Type_union --> lambda "rt" $
        Equality.equalString @@ (string $ unName _Type) @@ (unwrap _Name @@ (project _RowType _RowType_typeName @@ var "rt"))
--      Case _Type_variable --> constant true
    ]) @@ (ref stripTypeDef @@ var "t")

isUnitTermDef :: Definition (Term a -> Bool)
isUnitTermDef = basicsDefinition "isUnitTerm" $
  functionWithClasses termA booleanT eqA $
  lambda "t" $ Equality.equalTerm @@ (ref stripTermDef @@ var "t") @@ Datum (coreEncodeTerm Terms.unit)

isUnitTypeDef :: Definition (Term a -> Bool)
isUnitTypeDef = basicsDefinition "isUnitType" $
  functionWithClasses typeA booleanT eqA $
  lambda "t" $ Equality.equalType @@ (ref stripTypeDef @@ var "t") @@ Datum (coreEncodeType Types.unit)

elementsToGraphDef :: Definition (Graph a -> Maybe (Graph a) -> [Element a] -> Graph a)
elementsToGraphDef = basicsDefinition "elementsToGraph" $
  function graphA (functionT (Types.optional graphA) (functionT (TypeList elementA) graphA)) $
  lambda "parent" $ lambda "schema" $ lambda "elements" $
    Graph.graph
      (Maps.fromList @@ (Lists.map @@ var "toPair" @@ var "elements"))
      (Graph.graphEnvironment @@ var "parent")
      (Graph.graphTypes @@ var "parent")
      (Graph.graphBody @@ var "parent")
      (Graph.graphPrimitives @@ var "parent")
      (Graph.graphAnnotations @@ var "parent")
      (var "schema")
  `with` [
    "toPair" >: lambda "el" $ pair (project _Element _Element_name @@ var "el") (var "el")]

localNameOfEagerDef :: Definition (Name -> String)
localNameOfEagerDef = basicsDefinition "localNameOfEager" $
  function (TypeVariable _Name) (Types.string) $
  Module.qualifiedNameLocal <.> ref qualifyNameEagerDef

localNameOfLazyDef :: Definition (Name -> String)
localNameOfLazyDef = basicsDefinition "localNameOfLazy" $
  function (TypeVariable _Name) (Types.string) $
  Module.qualifiedNameLocal <.> ref qualifyNameLazyDef

namespaceOfEagerDef :: Definition (Name -> Maybe Namespace)
namespaceOfEagerDef = basicsDefinition "namespaceOfEager" $
  function (TypeVariable _Name) (Types.optional $ TypeVariable _Namespace) $
  Module.qualifiedNameNamespace <.> ref qualifyNameEagerDef

namespaceOfLazyDef :: Definition (Name -> Maybe Namespace)
namespaceOfLazyDef = basicsDefinition "namespaceOfLazy" $
  function (TypeVariable _Name) (Types.optional $ TypeVariable _Namespace) $
  Module.qualifiedNameNamespace <.> ref qualifyNameLazyDef

namespaceToFilePathDef :: Definition (Bool -> FileExtension -> Namespace -> String)
namespaceToFilePathDef = basicsDefinition "namespaceToFilePath" $
  function booleanT (functionT (TypeVariable _FileExtension) (functionT (TypeVariable _Namespace) Types.string)) $
  lambda "caps" $ lambda "ext" $ lambda "ns" $
    (((Strings.intercalate @@ "/" @@ var "parts") ++ "." ++ (unwrap _FileExtension @@ var "ext"))
    `with` [
      "parts">: Lists.map @@ (Logic.ifElse @@ ref capitalizeDef @@ ref idDef @@ var "caps") @@ (Strings.splitOn @@ "/" @@ (unwrap _Namespace @@ var "ns"))])

qualifyNameEagerDef :: Definition (Name -> QualifiedName)
qualifyNameEagerDef = basicsDefinition "qualifyNameEager" $
  lambda "name" $ ((Logic.ifElse
      @@ Module.qualifiedName nothing (unwrap _Name @@ var "name")
      @@ Module.qualifiedName
        (just $ wrap _Namespace (Lists.head @@ var "parts"))
        (Strings.intercalate @@ "." @@ (Lists.tail @@ var "parts"))
      @@ (Equality.equalInt32 @@ int32 1 @@ (Lists.length @@ var "parts")))
    `with` [
      "parts">: Strings.splitOn @@ "." @@ (unwrap _Name @@ var "name")])

qualifyNameLazyDef :: Definition (Name -> QualifiedName)
qualifyNameLazyDef = basicsDefinition "qualifyNameLazy" $
  lambda "name" $ (Logic.ifElse
      @@ Module.qualifiedName nothing (unwrap _Name @@ var "name")
      @@ Module.qualifiedName
        (just $ wrap _Namespace (Strings.intercalate @@ "." @@ (Lists.reverse @@ (Lists.tail @@ var "parts"))))
        (Lists.head @@ var "parts")
      @@ (Equality.equalInt32 @@ int32 1 @@ (Lists.length @@ var "parts")))
    `with` [
      "parts">: Lists.reverse @@ (Strings.splitOn @@ "." @@ (unwrap _Name @@ var "name"))]
