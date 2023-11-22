-- | A tier-2 module of basic functions for working with types and terms.

module Hydra.Basics where

import qualified Hydra.Core as Core
import qualified Hydra.Graph as Graph
import qualified Hydra.Lib.Equality as Equality
import qualified Hydra.Lib.Lists as Lists
import qualified Hydra.Lib.Logic as Logic
import qualified Hydra.Lib.Maps as Maps
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Mantle as Mantle
import qualified Hydra.Module as Module
import qualified Hydra.Strip as Strip
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | Find the elimination variant (constructor) for a given elimination term
eliminationVariant :: (Core.Elimination -> Mantle.EliminationVariant)
eliminationVariant x = case x of
  Core.EliminationList _ -> Mantle.EliminationVariantList
  Core.EliminationOptional _ -> Mantle.EliminationVariantOptional
  Core.EliminationProduct _ -> Mantle.EliminationVariantProduct
  Core.EliminationRecord _ -> Mantle.EliminationVariantRecord
  Core.EliminationUnion _ -> Mantle.EliminationVariantUnion
  Core.EliminationWrap _ -> Mantle.EliminationVariantWrap

-- | All elimination variants (constructors), in a canonical order
eliminationVariants :: [Mantle.EliminationVariant]
eliminationVariants = [
  Mantle.EliminationVariantList,
  Mantle.EliminationVariantWrap,
  Mantle.EliminationVariantOptional,
  Mantle.EliminationVariantProduct,
  Mantle.EliminationVariantRecord,
  Mantle.EliminationVariantUnion]

-- | Find the precision of a given floating-point type
floatTypePrecision :: (Core.FloatType -> Mantle.Precision)
floatTypePrecision x = case x of
  Core.FloatTypeBigfloat -> Mantle.PrecisionArbitrary
  Core.FloatTypeFloat32 -> (Mantle.PrecisionBits 32)
  Core.FloatTypeFloat64 -> (Mantle.PrecisionBits 64)

-- | All floating-point types in a canonical order
floatTypes :: [Core.FloatType]
floatTypes = [
  Core.FloatTypeBigfloat,
  Core.FloatTypeFloat32,
  Core.FloatTypeFloat64]

-- | Find the float type for a given floating-point value
floatValueType :: (Core.FloatValue -> Core.FloatType)
floatValueType x = case x of
  Core.FloatValueBigfloat _ -> Core.FloatTypeBigfloat
  Core.FloatValueFloat32 _ -> Core.FloatTypeFloat32
  Core.FloatValueFloat64 _ -> Core.FloatTypeFloat64

-- | Find the function variant (constructor) for a given function
functionVariant :: (Core.Function -> Mantle.FunctionVariant)
functionVariant x = case x of
  Core.FunctionElimination _ -> Mantle.FunctionVariantElimination
  Core.FunctionLambda _ -> Mantle.FunctionVariantLambda
  Core.FunctionPrimitive _ -> Mantle.FunctionVariantPrimitive

-- | All function variants (constructors), in a canonical order
functionVariants :: [Mantle.FunctionVariant]
functionVariants = [
  Mantle.FunctionVariantElimination,
  Mantle.FunctionVariantLambda,
  Mantle.FunctionVariantPrimitive]

-- | The identity function
id_ :: (a -> a)
id_ x = x

-- | Find whether a given integer type is signed (true) or unsigned (false)
integerTypeIsSigned :: (Core.IntegerType -> Bool)
integerTypeIsSigned x = case x of
  Core.IntegerTypeBigint -> True
  Core.IntegerTypeInt8 -> True
  Core.IntegerTypeInt16 -> True
  Core.IntegerTypeInt32 -> True
  Core.IntegerTypeInt64 -> True
  Core.IntegerTypeUint8 -> False
  Core.IntegerTypeUint16 -> False
  Core.IntegerTypeUint32 -> False
  Core.IntegerTypeUint64 -> False

-- | Find the precision of a given integer type
integerTypePrecision :: (Core.IntegerType -> Mantle.Precision)
integerTypePrecision x = case x of
  Core.IntegerTypeBigint -> Mantle.PrecisionArbitrary
  Core.IntegerTypeInt8 -> (Mantle.PrecisionBits 8)
  Core.IntegerTypeInt16 -> (Mantle.PrecisionBits 16)
  Core.IntegerTypeInt32 -> (Mantle.PrecisionBits 32)
  Core.IntegerTypeInt64 -> (Mantle.PrecisionBits 64)
  Core.IntegerTypeUint8 -> (Mantle.PrecisionBits 8)
  Core.IntegerTypeUint16 -> (Mantle.PrecisionBits 16)
  Core.IntegerTypeUint32 -> (Mantle.PrecisionBits 32)
  Core.IntegerTypeUint64 -> (Mantle.PrecisionBits 64)

-- | All integer types, in a canonical order
integerTypes :: [Core.IntegerType]
integerTypes = [
  Core.IntegerTypeBigint,
  Core.IntegerTypeInt8,
  Core.IntegerTypeInt16,
  Core.IntegerTypeInt32,
  Core.IntegerTypeInt64,
  Core.IntegerTypeUint8,
  Core.IntegerTypeUint16,
  Core.IntegerTypeUint32,
  Core.IntegerTypeUint64]

-- | Find the integer type for a given integer value
integerValueType :: (Core.IntegerValue -> Core.IntegerType)
integerValueType x = case x of
  Core.IntegerValueBigint _ -> Core.IntegerTypeBigint
  Core.IntegerValueInt8 _ -> Core.IntegerTypeInt8
  Core.IntegerValueInt16 _ -> Core.IntegerTypeInt16
  Core.IntegerValueInt32 _ -> Core.IntegerTypeInt32
  Core.IntegerValueInt64 _ -> Core.IntegerTypeInt64
  Core.IntegerValueUint8 _ -> Core.IntegerTypeUint8
  Core.IntegerValueUint16 _ -> Core.IntegerTypeUint16
  Core.IntegerValueUint32 _ -> Core.IntegerTypeUint32
  Core.IntegerValueUint64 _ -> Core.IntegerTypeUint64

-- | Find the literal type for a given literal value
literalType :: (Core.Literal -> Core.LiteralType)
literalType x = case x of
  Core.LiteralBinary _ -> Core.LiteralTypeBinary
  Core.LiteralBoolean _ -> Core.LiteralTypeBoolean
  Core.LiteralFloat v -> ((\x2 -> Core.LiteralTypeFloat x2) (floatValueType v))
  Core.LiteralInteger v -> ((\x2 -> Core.LiteralTypeInteger x2) (integerValueType v))
  Core.LiteralString _ -> Core.LiteralTypeString

-- | Find the literal type variant (constructor) for a given literal value
literalTypeVariant :: (Core.LiteralType -> Mantle.LiteralVariant)
literalTypeVariant x = case x of
  Core.LiteralTypeBinary -> Mantle.LiteralVariantBinary
  Core.LiteralTypeBoolean -> Mantle.LiteralVariantBoolean
  Core.LiteralTypeFloat _ -> Mantle.LiteralVariantFloat
  Core.LiteralTypeInteger _ -> Mantle.LiteralVariantInteger
  Core.LiteralTypeString -> Mantle.LiteralVariantString

-- | Find the literal variant (constructor) for a given literal value
literalVariant :: (Core.Literal -> Mantle.LiteralVariant)
literalVariant x = (literalTypeVariant (literalType x))

-- | All literal variants, in a canonical order
literalVariants :: [Mantle.LiteralVariant]
literalVariants = [
  Mantle.LiteralVariantBinary,
  Mantle.LiteralVariantBoolean,
  Mantle.LiteralVariantFloat,
  Mantle.LiteralVariantInteger,
  Mantle.LiteralVariantString]

termMeta :: (Graph.Graph -> Core.Term -> Core.Kv)
termMeta x = (Graph.annotationClassTermAnnotation (Graph.graphAnnotations x))

-- | Find the term variant (constructor) for a given term
termVariant :: (Core.Term -> Mantle.TermVariant)
termVariant x = case x of
  Core.TermAnnotated _ -> Mantle.TermVariantAnnotated
  Core.TermApplication _ -> Mantle.TermVariantApplication
  Core.TermFunction _ -> Mantle.TermVariantFunction
  Core.TermLet _ -> Mantle.TermVariantLet
  Core.TermList _ -> Mantle.TermVariantList
  Core.TermLiteral _ -> Mantle.TermVariantLiteral
  Core.TermMap _ -> Mantle.TermVariantMap
  Core.TermOptional _ -> Mantle.TermVariantOptional
  Core.TermProduct _ -> Mantle.TermVariantProduct
  Core.TermRecord _ -> Mantle.TermVariantRecord
  Core.TermSet _ -> Mantle.TermVariantSet
  Core.TermStream _ -> Mantle.TermVariantStream
  Core.TermSum _ -> Mantle.TermVariantSum
  Core.TermUnion _ -> Mantle.TermVariantUnion
  Core.TermVariable _ -> Mantle.TermVariantVariable
  Core.TermWrap _ -> Mantle.TermVariantWrap

-- | All term (expression) variants, in a canonical order
termVariants :: [Mantle.TermVariant]
termVariants = [
  Mantle.TermVariantAnnotated,
  Mantle.TermVariantApplication,
  Mantle.TermVariantLiteral,
  Mantle.TermVariantFunction,
  Mantle.TermVariantList,
  Mantle.TermVariantMap,
  Mantle.TermVariantOptional,
  Mantle.TermVariantProduct,
  Mantle.TermVariantRecord,
  Mantle.TermVariantSet,
  Mantle.TermVariantStream,
  Mantle.TermVariantSum,
  Mantle.TermVariantUnion,
  Mantle.TermVariantVariable,
  Mantle.TermVariantWrap]

-- | Find the type variant (constructor) for a given type
typeVariant :: (Core.Type -> Mantle.TypeVariant)
typeVariant x = case x of
  Core.TypeAnnotated _ -> Mantle.TypeVariantAnnotated
  Core.TypeApplication _ -> Mantle.TypeVariantApplication
  Core.TypeFunction _ -> Mantle.TypeVariantFunction
  Core.TypeLambda _ -> Mantle.TypeVariantLambda
  Core.TypeList _ -> Mantle.TypeVariantList
  Core.TypeLiteral _ -> Mantle.TypeVariantLiteral
  Core.TypeMap _ -> Mantle.TypeVariantMap
  Core.TypeOptional _ -> Mantle.TypeVariantOptional
  Core.TypeProduct _ -> Mantle.TypeVariantProduct
  Core.TypeRecord _ -> Mantle.TypeVariantRecord
  Core.TypeSet _ -> Mantle.TypeVariantSet
  Core.TypeStream _ -> Mantle.TypeVariantStream
  Core.TypeSum _ -> Mantle.TypeVariantSum
  Core.TypeUnion _ -> Mantle.TypeVariantUnion
  Core.TypeVariable _ -> Mantle.TypeVariantVariable
  Core.TypeWrap _ -> Mantle.TypeVariantWrap

-- | All type variants, in a canonical order
typeVariants :: [Mantle.TypeVariant]
typeVariants = [
  Mantle.TypeVariantAnnotated,
  Mantle.TypeVariantApplication,
  Mantle.TypeVariantFunction,
  Mantle.TypeVariantLambda,
  Mantle.TypeVariantList,
  Mantle.TypeVariantLiteral,
  Mantle.TypeVariantMap,
  Mantle.TypeVariantWrap,
  Mantle.TypeVariantOptional,
  Mantle.TypeVariantProduct,
  Mantle.TypeVariantRecord,
  Mantle.TypeVariantSet,
  Mantle.TypeVariantStream,
  Mantle.TypeVariantSum,
  Mantle.TypeVariantUnion,
  Mantle.TypeVariantVariable]

-- | Capitalize the first letter of a string
capitalize :: (String -> String)
capitalize = (mapFirstLetter Strings.toUpper)

-- | Decapitalize the first letter of a string
decapitalize :: (String -> String)
decapitalize = (mapFirstLetter Strings.toLower)

-- | A helper which maps the first letter of a string to another string
mapFirstLetter :: ((String -> String) -> String -> String)
mapFirstLetter mapping s =  
  let firstLetter = (mapping (Strings.fromList (Lists.pure (Lists.head list)))) 
      list = (Strings.toList s)
  in (Logic.ifElse s (Strings.cat2 firstLetter (Strings.fromList (Lists.tail list))) (Strings.isEmpty s))

fieldMap :: ([Core.Field] -> Map Core.FieldName (Core.Term))
fieldMap fields = (Maps.fromList (Lists.map toPair fields)) 
  where 
    toPair = (\f -> (Core.fieldName f, (Core.fieldTerm f)))

fieldTypeMap :: ([Core.FieldType] -> Map Core.FieldName (Core.Type))
fieldTypeMap fields = (Maps.fromList (Lists.map toPair fields)) 
  where 
    toPair = (\f -> (Core.fieldTypeName f, (Core.fieldTypeType f)))

isEncodedType :: (Core.Term -> Bool)
isEncodedType t = ((\x -> case x of
  Core.TermApplication v -> (isEncodedType (Core.applicationFunction v))
  Core.TermUnion v -> (Equality.equalString "hydra/core.Type" (Core.unName (Core.injectionTypeName v)))
  _ -> False) (Strip.stripTerm t))

isType :: (Core.Type -> Bool)
isType t = ((\x -> case x of
  Core.TypeVariable (Core.Name "hydra/core.Type") -> True
  _ -> False) (Strip.stripType t))

isUnitTerm :: (Core.Term -> Bool)
isUnitTerm t = (Equality.equalTerm (Strip.stripTerm t) (Core.TermRecord (Core.Record {
  Core.recordTypeName = (Core.Name "hydra/core.UnitType"),
  Core.recordFields = []})))

isUnitType :: (Core.Type -> Bool)
isUnitType t = (Equality.equalType (Strip.stripType t) (Core.TypeRecord (Core.RowType {
  Core.rowTypeTypeName = (Core.Name "hydra/core.UnitType"),
  Core.rowTypeExtends = Nothing,
  Core.rowTypeFields = []})))

elementsToGraph :: (Graph.Graph -> Maybe (Graph.Graph) -> [Graph.Element] -> Graph.Graph)
elementsToGraph parent schema elements =  
  let toPair = (\el -> (Graph.elementName el, el))
  in Graph.Graph {
    Graph.graphElements = (Maps.fromList (Lists.map toPair elements)),
    Graph.graphEnvironment = (Graph.graphEnvironment parent),
    Graph.graphTypes = (Graph.graphTypes parent),
    Graph.graphBody = (Graph.graphBody parent),
    Graph.graphPrimitives = (Graph.graphPrimitives parent),
    Graph.graphAnnotations = (Graph.graphAnnotations parent),
    Graph.graphSchema = schema}

localNameOfEager :: (Core.Name -> String)
localNameOfEager x = (Module.qualifiedNameLocal (qualifyNameEager x))

localNameOfLazy :: (Core.Name -> String)
localNameOfLazy x = (Module.qualifiedNameLocal (qualifyNameLazy x))

namespaceOfEager :: (Core.Name -> Maybe Module.Namespace)
namespaceOfEager x = (Module.qualifiedNameNamespace (qualifyNameEager x))

namespaceOfLazy :: (Core.Name -> Maybe Module.Namespace)
namespaceOfLazy x = (Module.qualifiedNameNamespace (qualifyNameLazy x))

namespaceToFilePath :: (Bool -> Module.FileExtension -> Module.Namespace -> String)
namespaceToFilePath caps ext ns =  
  let parts = (Lists.map (Logic.ifElse capitalize id_ caps) (Strings.splitOn "/" (Module.unNamespace ns)))
  in (Strings.cat [
    Strings.cat [
      Strings.intercalate "/" parts,
      "."],
    (Module.unFileExtension ext)])

qualifyNameEager :: (Core.Name -> Module.QualifiedName)
qualifyNameEager name =  
  let parts = (Strings.splitOn "." (Core.unName name))
  in (Logic.ifElse (Module.QualifiedName {
    Module.qualifiedNameNamespace = Nothing,
    Module.qualifiedNameLocal = (Core.unName name)}) (Module.QualifiedName {
    Module.qualifiedNameNamespace = (Just (Module.Namespace (Lists.head parts))),
    Module.qualifiedNameLocal = (Strings.intercalate "." (Lists.tail parts))}) (Equality.equalInt32 1 (Lists.length parts)))

qualifyNameLazy :: (Core.Name -> Module.QualifiedName)
qualifyNameLazy name =  
  let parts = (Lists.reverse (Strings.splitOn "." (Core.unName name)))
  in (Logic.ifElse (Module.QualifiedName {
    Module.qualifiedNameNamespace = Nothing,
    Module.qualifiedNameLocal = (Core.unName name)}) (Module.QualifiedName {
    Module.qualifiedNameNamespace = (Just (Module.Namespace (Strings.intercalate "." (Lists.reverse (Lists.tail parts))))),
    Module.qualifiedNameLocal = (Lists.head parts)}) (Equality.equalInt32 1 (Lists.length parts)))
