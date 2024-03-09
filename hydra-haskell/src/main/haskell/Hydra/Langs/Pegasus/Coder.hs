module Hydra.Langs.Pegasus.Coder (moduleToPdl) where

import Hydra.Kernel
import Hydra.TermAdapters
import Hydra.Adapters
import Hydra.Langs.Pegasus.Language
import Hydra.Tools.Serialization
import Hydra.Langs.Pegasus.Serde
import qualified Hydra.Langs.Pegasus.Pdl as PDL
import qualified Hydra.Dsl.Types as Types

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


moduleToPdl :: Module -> Flow Graph (M.Map FilePath String)
moduleToPdl mod = do
    files <- moduleToPegasusSchemas mod
    return $ M.fromList (mapPair <$> M.toList files)
  where
    mapPair (path, sf) = (path, printExpr $ parenthesize $ exprSchemaFile sf)

constructModule ::
  M.Map Namespace String
  -> Module
  -> M.Map Type (Coder Graph Graph Term ())
  -> [Element]
  -> Flow Graph (M.Map FilePath PDL.SchemaFile)
constructModule aliases mod coders els = do
    pairs <- CM.mapM toLegacyPair els
    let pairByName = L.foldl (\m p -> M.insert (elementName $ fst p) p m) M.empty pairs
    sortedPairs <- case (topologicalSortElements els) of
      Left comps -> fail $ "types form a cycle (unsupported in PDL): " ++ show (L.head comps)
      Right sorted -> pure $ Y.catMaybes $ fmap (\n -> M.lookup n pairByName) sorted
    schemas <- CM.mapM toSchema sortedPairs
    return $ M.fromList (toPair <$> schemas)
  where
    toLegacyPair el = do
      let term = elementData el
      typ <- requireTermType term
      return (el, TypedTerm typ term)
    ns = pdlNameForModule mod
    pkg = Nothing
    toPair (schema, imports) = (path, PDL.SchemaFile ns pkg imports [schema])
      where
        path = namespaceToFilePath False (FileExtension "pdl") (Namespace $ (unNamespace $ moduleNamespace mod) ++ "/" ++ local)
        local = PDL.unName $ PDL.qualifiedNameName $ PDL.namedSchemaQualifiedName schema

    toSchema (el, TypedTerm typ term) = do
      if isType typ
        then coreDecodeType term >>= typeToSchema el
        else fail $ "mapping of non-type elements to PDL is not yet supported: " ++ unName (elementName el)
    typeToSchema el typ = do
        res <- encodeAdaptedType aliases typ
        let ptype = case res of
              Left schema -> PDL.NamedSchema_TypeTyperef schema
              Right t -> t
        r <- getTermDescription $ elementData el
        let anns = doc r
        return (PDL.NamedSchema qname ptype anns, imports)
      where
        qname = pdlNameForElement aliases False $ elementName el
        imports = []
--        imports = L.filter isExternal (pdlNameForElement aliases True <$> deps)
--          where
--            deps = S.toList $ termDependencyNames False False False $ elementData el
--            isExternal qn = PDL.qualifiedNameNamespace qn /= PDL.qualifiedNameNamespace qname

moduleToPegasusSchemas :: Module -> Flow Graph (M.Map FilePath PDL.SchemaFile)
moduleToPegasusSchemas mod = do
  aliases <- importAliasesForModule mod
  transformModule pdlLanguage (encodeTerm aliases) (constructModule aliases) mod

doc :: Y.Maybe String -> PDL.Annotations
doc s = PDL.Annotations s False

encodeAdaptedType ::
  M.Map Namespace String -> Type
  -> Flow Graph (Either PDL.Schema PDL.NamedSchema_Type)
encodeAdaptedType aliases typ = do
  g <- getState
  let cx = AdapterContext g pdlLanguage M.empty
  ad <- withState cx $ termAdapter typ
  encodeType aliases $ adapterTarget ad

encodeTerm :: M.Map Namespace String -> Term -> Flow Graph ()
encodeTerm aliases term = fail "not yet implemented"

encodeType :: M.Map Namespace String -> Type -> Flow Graph (Either PDL.Schema PDL.NamedSchema_Type)
encodeType aliases typ = case typ of
    TypeAnnotated (Annotated typ' _) -> encodeType aliases typ'
    TypeList lt -> Left . PDL.SchemaArray <$> encode lt
    TypeLiteral lt -> Left . PDL.SchemaPrimitive <$> case lt of
      LiteralTypeBinary -> pure PDL.PrimitiveTypeBytes
      LiteralTypeBoolean -> pure PDL.PrimitiveTypeBoolean
      LiteralTypeFloat ft -> case ft of
        FloatTypeFloat32 -> pure PDL.PrimitiveTypeFloat
        FloatTypeFloat64 -> pure PDL.PrimitiveTypeDouble
        _ -> unexpected "float32 or float64" $ show ft
      LiteralTypeInteger it -> case it of
        IntegerTypeInt32 -> pure PDL.PrimitiveTypeInt
        IntegerTypeInt64 -> pure PDL.PrimitiveTypeLong
        _ -> unexpected "int32 or int64" $ show it
      LiteralTypeString -> pure PDL.PrimitiveTypeString
    TypeMap (MapType kt vt) -> Left . PDL.SchemaMap <$> encode vt -- note: we simply assume string as a key type
    TypeVariable name -> pure $ Left $ PDL.SchemaNamed $ pdlNameForElement aliases True name
    TypeOptional ot -> fail $ "optionals unexpected at top level"
    TypeRecord rt -> do
      let includes = []
      rfields <- CM.mapM encodeRecordField $ rowTypeFields rt
      return $ Right $ PDL.NamedSchema_TypeRecord $ PDL.RecordSchema rfields includes
    TypeUnion rt -> if isEnum
        then do
          fs <- CM.mapM encodeEnumField $ rowTypeFields rt
          return $ Right $ PDL.NamedSchema_TypeEnum $ PDL.EnumSchema fs
        else Left . PDL.SchemaUnion . PDL.UnionSchema <$> CM.mapM encodeUnionField (rowTypeFields rt)
      where
        isEnum = L.foldl (\b t -> b && stripType t == Types.unit) True $ fmap fieldTypeType (rowTypeFields rt)
    _ -> unexpected "PDL-supported type" $ show typ
  where
    encode t = case stripType t of
      TypeRecord (RowType _ Nothing []) -> encode Types.int32 -- special case for the unit type
      _ -> do
        res <- encodeType aliases t
        case res of
          Left schema -> pure schema
          Right _ -> fail $ "type resolved to an unsupported nested named schema: " ++ show t
    encodeRecordField (FieldType (FieldName name) typ) = do
      anns <- getAnns typ
      (schema, optional) <- encodePossiblyOptionalType typ
      return PDL.RecordField {
        PDL.recordFieldName = PDL.FieldName name,
        PDL.recordFieldValue = schema,
        PDL.recordFieldOptional = optional,
        PDL.recordFieldDefault = Nothing,
        PDL.recordFieldAnnotations = anns}
    encodeUnionField (FieldType (FieldName name) typ) = do
      anns <- getAnns typ
      (s, optional) <- encodePossiblyOptionalType typ
      let schema = if optional
          then PDL.SchemaUnion $ PDL.UnionSchema (simpleUnionMember <$> [PDL.SchemaNull, s])
          else s
      return PDL.UnionMember {
        PDL.unionMemberAlias = Just $ PDL.FieldName name,
        PDL.unionMemberValue = schema,
        PDL.unionMemberAnnotations = anns}
    encodeEnumField (FieldType (FieldName name) typ) = do
      anns <- getAnns typ
      return PDL.EnumField {
        PDL.enumFieldName = PDL.EnumFieldName $ convertCase CaseConventionCamel CaseConventionUpperSnake name,
        PDL.enumFieldAnnotations = anns}
    encodePossiblyOptionalType typ = case stripType typ of
      TypeOptional ot -> do
        t <- encode ot
        return (t, True)
      _ -> do
        t <- encode typ
        return (t, False)
    getAnns typ = do
      r <- getTypeDescription typ
      return $ doc r

importAliasesForModule mod = do
    nss <- moduleDependencyNamespaces False True True False mod
    return $ M.fromList (toPair <$> S.toList nss)
  where
    toPair ns = (ns, slashesToDots $ unNamespace ns)

noAnnotations :: PDL.Annotations
noAnnotations = PDL.Annotations Nothing False

pdlNameForElement :: M.Map Namespace String -> Bool -> Name -> PDL.QualifiedName
pdlNameForElement aliases withNs name = PDL.QualifiedName (PDL.Name local)
    $ if withNs
      then PDL.Namespace <$> alias
      else Nothing
  where
    QualifiedName (Just ns) local = qualifyNameEager name
    alias = M.lookup ns aliases

pdlNameForModule :: Module -> PDL.Namespace
pdlNameForModule = PDL.Namespace . slashesToDots . h . moduleNamespace
  where
    h (Namespace n) = n

simpleUnionMember :: PDL.Schema -> PDL.UnionMember
simpleUnionMember schema = PDL.UnionMember Nothing schema noAnnotations

slashesToDots :: String -> String
slashesToDots = fmap (\c -> if c == '/' then '.' else c)
