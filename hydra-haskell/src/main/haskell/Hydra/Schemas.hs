-- | Various functions for dereferencing and decoding schema types

module Hydra.Schemas (
  Definition(..),
  Namespaces(..),
  definitionDependencyNamespaces,
  dependencyNamespaces,
  elementAsTypedTerm,
  fieldTypes,
  isEnumType,
  isSerializable,
  moduleDependencyNamespaces,
  namespacesForDefinitions,
  requireRecordType,
  requireType,
  requireUnionType,
  requireWrappedType,
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
import Hydra.Tier1
import Hydra.Tier2
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


data Definition = DefinitionType Name Type | DefinitionTerm Name Term Type

data Namespaces n = Namespaces {
  namespacesFocus :: (Namespace, n),
  namespacesMapping :: M.Map Namespace n} deriving Show

definitionDependencyNamespaces :: [Definition] -> S.Set Namespace
definitionDependencyNamespaces defs = S.fromList $ Y.catMaybes (namespaceOfEager <$> S.toList allNames)
  where
    allNames = S.unions (defNames <$> defs)
    defNames def = case def of
        DefinitionType _ typ -> typeDependencyNames typ
        DefinitionTerm _ term _ -> termDependencyNames True True True term

-- | Find dependency namespaces in all of a set of terms.
dependencyNamespaces :: Bool -> Bool -> Bool -> Bool -> [Term] -> Flow Graph (S.Set Namespace)
dependencyNamespaces withVars withPrims withNoms withSchema terms = do
    allNames <- S.unions <$> (CM.mapM depNames terms)
    return $ S.fromList $ Y.catMaybes (namespaceOfEager <$> S.toList allNames)
  where
    depNames term = do
      let dataNames = termDependencyNames withVars withPrims withNoms term

      schemaNames <- if withSchema
        then typeDependencyNames <$> requireTermType term
        else pure S.empty

      typeNames <- if isEncodedType (fullyStripTerm term)
        then typeDependencyNames <$> coreDecodeType term
        else pure S.empty

      return $ S.unions [dataNames, schemaNames, typeNames]

dereferenceType :: Name -> Flow Graph (Maybe Type)
dereferenceType name = do
  mel <- dereferenceElement name
  case mel of
    Nothing -> return Nothing
    Just el -> Just <$> coreDecodeType (elementData el)

elementAsTypedTerm :: Element -> Flow Graph TypedTerm
elementAsTypedTerm el = do
  typ <- requireTermType $ elementData el
  return $ TypedTerm (elementData el) typ

fieldTypes :: Type -> Flow Graph (M.Map Name Type)
fieldTypes t = case stripType t of
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

-- | Checks whether the fields of a 'RowType' are all unit-typed.
--   A union with such a 'RowType' can be treated as an enum in languages that support enums.
isEnumType :: RowType -> Bool
isEnumType (RowType _ tfields) = L.foldl (\b f -> b && isUnitType (fieldTypeType f)) True tfields

isSerializable :: Element -> Flow Graph Bool
isSerializable el = do
    deps <- typeDependencies id (elementName el)
    let allVariants = S.fromList $ L.concat (variants <$> M.elems deps)
    return $ not $ S.member TypeVariantFunction allVariants
  where
    variants typ = typeVariant <$> foldOverType TraversalOrderPre (\m t -> t:m) [] typ

-- | Find dependency namespaces in all of the elements of a module, excluding the module's own namespace.
moduleDependencyNamespaces :: Bool -> Bool -> Bool -> Bool -> Module -> Flow Graph (S.Set Namespace)
moduleDependencyNamespaces withVars withPrims withNoms withSchema mod =
  S.delete (moduleNamespace mod) <$> (dependencyNamespaces withVars withPrims withNoms withSchema $
    (elementData <$> moduleElements mod))

namespacesForDefinitions :: (Namespace -> a) -> Namespace -> [Definition] -> Namespaces a
namespacesForDefinitions encodeNamespace focusNs defs = Namespaces (toPair focusNs) $ M.fromList (toPair <$> S.toList nss)
  where
    nss = S.delete focusNs $ definitionDependencyNamespaces defs
    toPair ns = (ns, encodeNamespace ns)

requireRecordType :: Name -> Flow Graph RowType
requireRecordType = requireRowType "record type" $ \t -> case t of
  TypeRecord rt -> Just rt
  _ -> Nothing

requireRowType :: String -> (Type -> Maybe RowType) -> Name -> Flow Graph RowType
requireRowType label getter name = do
  t <- requireType name
  case getter (rawType t) of
    Just rt -> return rt
    Nothing -> fail $ show name ++ " does not resolve to a " ++ label ++ " type: " ++ show t
  where
    rawType t = case t of
      TypeAnnotated (AnnotatedType t' _) -> rawType t'
      TypeLambda (LambdaType _ body) -> rawType body -- Note: throwing away quantification here
      _ -> t

requireType :: Name -> Flow Graph Type
requireType name = withTrace ("require type " ++ unName name) $
  (withSchemaContext $ requireElement name) >>= (coreDecodeType . elementData)

requireUnionType :: Name -> Flow Graph RowType
requireUnionType = requireRowType "union" $ \t -> case t of
  TypeUnion rt -> Just rt
  _ -> Nothing

requireWrappedType :: Name -> Flow Graph Type
requireWrappedType name = do
  typ <- requireType name
  case stripType typ of
    TypeWrap (WrappedType name t) -> return t
    _ -> return typ -- TODO: stop allowing this "slop" once typedefs are clearly separated from newtypes
--     _ -> fail $ "expected wrapped type for " ++ unName name ++ " but got " ++ show typ

resolveType :: Type -> Flow Graph (Maybe Type)
resolveType typ = case stripType typ of
    TypeVariable name -> withSchemaContext $ do
      mterm <- resolveTerm name
      case mterm of
        Nothing -> pure Nothing
        Just t -> Just <$> coreDecodeType t
    _ -> pure $ Just typ

typeDependencies :: (Type -> Type) -> Name -> Flow Graph (M.Map Name Type)
typeDependencies transform name = deps (S.fromList [name]) M.empty
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
          typ <- transform <$> requireType name
          return (name, typ)

    requireType name = do
      withTrace ("type dependencies of " ++ unName name) $ do
        el <- requireElement name
        coreDecodeType (elementData el)