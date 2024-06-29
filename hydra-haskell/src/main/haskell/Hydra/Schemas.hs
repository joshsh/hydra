-- | Various functions for dereferencing and decoding schema types

module Hydra.Schemas (
  fieldTypes,
  getTyped,
  isSerializable,
  moduleDependencyNamespaces,
  requirePrimitiveType,
  toRecordType,
  requireType,
  toUnionType,
  toWrappedType,
  resolveType,
  typeDependencies,
  typeDependencyNames,
  ) where

import Hydra.Basics
import Hydra.Strip
import Hydra.Coders
import Hydra.Compute
import Hydra.Core
import Hydra.CoreDecoding
import Hydra.Graph
import Hydra.Mantle
import Hydra.Module
import Hydra.Lexical
import Hydra.Rewriting
import Hydra.Substitution
import Hydra.Tier1
import Hydra.Tier2
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


dereferenceType :: Name -> Flow Graph (Maybe Type)
dereferenceType name = withTrace ("dereference" ++ unName name) $ do
  mel <- dereferenceElement name
  case mel of
    Nothing -> return Nothing
    Just el -> Just <$> coreDecodeType (elementData el)

fieldTypes :: Type -> Flow Graph (M.Map Name Type)
fieldTypes t = withTrace "field types" $ case stripType t of
    TypeLambda (LambdaType _ body) -> fieldTypes body
    TypeRecord rt -> pure $ toMap $ rowTypeFields rt
    TypeUnion rt -> pure $ toMap $ rowTypeFields rt
    TypeVariable name -> do
      withTrace ("field types of " ++ unName name) $ do
        el <- requireElement name
        coreDecodeType (elementData el) >>= fieldTypes
    _ -> unexpected "record or union type" $ show t
  where
    toMap fields = M.fromList (toPair <$> fields)
    toPair (FieldType fname ftype) = (fname, ftype)

getTyped :: Term -> Maybe Type
getTyped term = case term of
  TermAnnotated (Annotated t _) -> getTyped t
  TermTyped (TypedTerm typ _) -> Just typ
  _ -> Nothing

isSerializable :: Element -> Flow Graph Bool
isSerializable el = do
    deps <- typeDependencies (elementName el)
    let allVariants = S.fromList $ L.concat (variants <$> M.elems deps)
    return $ not $ S.member TypeVariantFunction allVariants
  where
    variants typ = typeVariant <$> foldOverType TraversalOrderPre (\m t -> t:m) [] typ

-- | Find dependency namespaces in various dimensions of a term
moduleDependencyNamespaces :: Bool -> Bool -> Bool -> Bool -> Module -> Flow Graph (S.Set Namespace)
moduleDependencyNamespaces withVars withPrims withNoms withSchema mod = withTrace "dependency namespaces" $ do
    allNames <- S.unions <$> (CM.mapM elNames $ moduleElements mod)
    let namespaces = S.fromList $ Y.catMaybes (namespaceOfEager <$> S.toList allNames)
    return $ S.delete (moduleNamespace mod) namespaces
  where
    elNames el = withTrace ("for element " ++ unName (elementName el)) $ do
      let term = elementData el
      let dataNames = termDependencyNames withVars withPrims withNoms term
      schemaNames <- if withSchema
        then typeDependencyNames <$> requireTermType term
        else pure S.empty

      typeNames <- if isEncodedType term
        then typeDependencyNames <$> coreDecodeType term
        else pure S.empty
      return $ S.unions [dataNames, schemaNames, typeNames]

-- | Resolve a name to the type of the corresponding primitive, replacing any bound type variables with temporary variables
requirePrimitiveType :: Name -> Flow Graph Type
requirePrimitiveType name = (primitiveType <$> requirePrimitive name) >>= instantiate

requireType :: Name -> Flow Graph Type
requireType name = withTrace ("require type " ++ unName name) $
  requireElement name >>= (coreDecodeType . elementData) >>= instantiate

-- TODO: remove this function once TermAdapters no longer needs it
resolveType :: Type -> Flow Graph (Maybe Type)
resolveType typ = withTrace "resolve type" $ case stripType typ of
    TypeVariable name -> withSchemaContext $ do
      mterm <- resolveTerm name
      case mterm of
        Nothing -> pure Nothing
        Just t -> Just <$> coreDecodeType t
    _ -> pure $ Just typ

toRecordType :: Name -> Type -> Flow Graph RowType
toRecordType = toRowType "record" getType
  where
    getType t = case stripType t of
      TypeLambda (LambdaType _ body) -> getType body
      TypeRecord rt -> Just rt
      _ -> Nothing

toRowType :: String -> (Type -> Maybe RowType) -> Name -> Type -> Flow Graph RowType
toRowType label getter name t = do
  case getter (rawType t) of
    Just rt -> return rt
    Nothing -> fail $ show name ++ " does not resolve to a " ++ label ++ " type: " ++ show t
  where
    rawType t = case t of
      TypeAnnotated (Annotated t' _) -> rawType t'
      TypeLambda (LambdaType _ body) -> rawType body -- Note: throwing away quantification here
      _ -> t

toUnionType :: Name -> Type -> Flow Graph RowType
toUnionType = toRowType "union" getType
  where
    getType t = case stripType t of
      TypeLambda (LambdaType _ body) -> getType body
      TypeUnion rt -> Just rt
      _ -> Nothing

toWrappedType :: Name -> Type -> Flow Graph Type
toWrappedType name typ = case stripType typ of
    TypeLambda (LambdaType _ body) -> toWrappedType name body
    TypeWrap (Nominal name t) -> return t
    _ -> return typ -- TODO: stop allowing this "slop" once typedefs are clearly separated from newtypes
--     _ -> fail $ "expected wrapped type for " ++ unName name ++ " but got " ++ show typ

typeDependencies :: Name -> Flow Graph (M.Map Name Type)
typeDependencies name = withTrace ("dependencies of " ++ unName name) $ deps (S.fromList [name]) M.empty
  where
    deps seeds names = if S.null seeds
        then return names
        else do
          pairs <- CM.mapM toPair $ S.toList seeds
          let newNames = M.union names (M.fromList pairs)
          let refs = L.foldl S.union S.empty (typeDependencyNames <$> (snd <$> pairs))
          let visited = S.fromList $ M.keys names
          let newSeeds = S.difference refs visited
          deps newSeeds newNames
      where
        toPair name = do
          typ <- requireType name
          return (name, typ)

    requireType name = do
      withTrace ("type dependencies of " ++ unName name) $ do
        el <- requireElement name
        coreDecodeType (elementData el)
