-- | Functions for working with Kv, the default annotation type in Hydra

module Hydra.Kv where

import Hydra.Basics
import Hydra.Strip
import Hydra.Core
import Hydra.Compute
import Hydra.Extras
import Hydra.Graph
import Hydra.CoreDecoding
import Hydra.CoreEncoding
import Hydra.Lexical
import Hydra.Mantle
import Hydra.Tier1
import Hydra.Tier2
import qualified Hydra.Dsl.Expect as Expect
import Hydra.Tools.Debug

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


kvClasses = "classes" :: String
kvDescription = "description" :: String
kvType = "type" :: String

aggregateAnnotations :: (x -> Maybe (Annotated x)) -> x -> Kv
aggregateAnnotations getAnn t = Kv $ M.fromList $ L.concat $ toPairs [] t
  where
    toPairs rest t = case getAnn t of
      Nothing -> rest
      Just (Annotated t' (Kv other)) -> toPairs ((M.toList other):rest) t'

failOnFlag :: String -> String -> Flow s ()
failOnFlag flag msg = do
  val <- hasFlag flag
  if val
    then fail msg
    else pure ()

getAnnotatedType :: Term -> Flow Graph (Y.Maybe Type)
getAnnotatedType = getType . termAnnotation

getAttr :: String -> Flow s (Maybe Term)
getAttr key = Flow q
  where
    q s0 t0 = FlowState (Just $ M.lookup key $ traceOther t0) s0 t0

getAttrWithDefault :: String -> Term -> Flow s Term
getAttrWithDefault key def = Y.fromMaybe def <$> getAttr key

getDescription :: Kv -> Flow Graph (Y.Maybe String)
getDescription kv = case getAnnotation kvDescription kv of
  Nothing -> pure Nothing
  Just term -> case term of
    TermLiteral (LiteralString s) -> pure $ Just s
    _ -> fail $ "unexpected value for " ++ show kvDescription ++ ": " ++ show term

getTermAnnotation :: String -> Term -> Y.Maybe Term
getTermAnnotation key = getAnnotation key . termAnnotation

getTermDescription :: Term -> Flow Graph (Y.Maybe String)
getTermDescription = getDescription . termAnnotation

getType :: Kv -> Flow Graph (Y.Maybe Type)
getType kv = case getAnnotation kvType kv of
  Nothing -> pure Nothing
  Just dat -> Just <$> coreDecodeType dat

getTypeAnnotation :: String -> Type -> Y.Maybe Term
getTypeAnnotation key = getAnnotation key . typeAnnotation

getTypeClasses :: Type -> Flow Graph (M.Map Name (S.Set TypeClass))
getTypeClasses typ = case getTypeAnnotation kvClasses typ of
    Nothing -> pure M.empty
    Just term -> Expect.map coreDecodeName (Expect.set decodeClass) term
  where
    decodeClass term = Expect.unitVariant _TypeClass term >>= \fn -> Y.maybe
      (unexpected "type class" $ show term) pure $ M.lookup fn byName
    byName = M.fromList [(_TypeClass_equality, TypeClassEquality), (_TypeClass_ordering, TypeClassOrdering)]

getTypeDescription :: Type -> Flow Graph (Y.Maybe String)
getTypeDescription = getDescription . typeAnnotation

hasFlag :: String -> Flow s Bool
hasFlag flag = getAttrWithDefault flag (TermLiteral $ LiteralBoolean False) >>= Expect.boolean

kvAnnotationClass :: AnnotationClass
kvAnnotationClass = AnnotationClass {
    annotationClassTermAnnotation = termAnnotation,
    annotationClassTypeAnnotation = typeAnnotation,
    annotationClassTermDescription = getTermDescription,
    annotationClassTypeDescription = getTypeDescription,
    annotationClassTypeClasses = getTypeClasses,
    annotationClassTermType = getAnnotatedType,
    annotationClassSetTermDescription = setTermDescription,
    annotationClassSetTermType = setTermType,
    annotationClassSetTypeClasses = setTypeClasses,
    annotationClassTypeOf = getType,
    annotationClassSetTypeOf = setType}

-- | Return a zero-indexed counter for the given key: 0, 1, 2, ...
nextCount :: String -> Flow s Int
nextCount attrName = do
  count <- getAttrWithDefault attrName (TermLiteral $ LiteralInteger $ IntegerValueInt32 0) >>= Expect.int32
  putAttr attrName (TermLiteral $ LiteralInteger $ IntegerValueInt32 $ count + 1)
  return count

resetCount :: String -> Flow s ()
resetCount attrName = do
  putAttr attrName (TermLiteral $ LiteralInteger $ IntegerValueInt32 0)
  return ()

normalizeTermAnnotations :: Term -> Term
normalizeTermAnnotations term = if M.null (kvAnnotations kv)
    then stripped
    else TermAnnotated $ Annotated stripped kv
  where
    kv = termAnnotation term
    stripped = stripTerm term

normalizeTypeAnnotations :: Type -> Type
normalizeTypeAnnotations typ = if M.null (kvAnnotations kv)
    then stripped
    else TypeAnnotated $ Annotated stripped kv
  where
    kv = typeAnnotation typ
    stripped = stripType typ

putAttr :: String -> Term -> Flow s ()
putAttr key val = Flow q
  where
    q s0 t0 = FlowState (Just ()) s0 (t0 {traceOther = M.insert key val $ traceOther t0})

setAnnotation :: String -> Y.Maybe Term -> Kv -> Kv
setAnnotation key val (Kv m) = Kv $ M.alter (const val) key m

setDescription :: Y.Maybe String -> Kv -> Kv
setDescription d = setAnnotation kvDescription (TermLiteral . LiteralString <$> d)

setTermAnnotation :: String -> Y.Maybe Term -> Term -> Term
setTermAnnotation key val term = if kv == Kv M.empty
    then term'
    else TermAnnotated $ Annotated term' kv
  where
    term' = stripTerm term
    kv = setAnnotation key val $ termAnnotation term

setTermDescription :: Y.Maybe String -> Term -> Term
setTermDescription d = setTermAnnotation kvDescription (TermLiteral . LiteralString <$> d)

setTermType :: Y.Maybe Type -> Term -> Term
setTermType d = setTermAnnotation kvType (coreEncodeType <$> d)

setType :: Y.Maybe Type -> Kv -> Kv
setType mt = setAnnotation kvType (coreEncodeType <$> mt)

setTypeAnnotation :: String -> Y.Maybe Term -> Type -> Type
setTypeAnnotation key val typ = if kv == Kv M.empty
    then typ'
    else TypeAnnotated $ Annotated typ' kv
  where
    typ' = stripType typ
    kv = setAnnotation key val $ typeAnnotation typ

setTypeClasses :: M.Map Name (S.Set TypeClass) -> Type -> Type
setTypeClasses m = setTypeAnnotation kvClasses encoded
  where
    encoded = if M.null m
      then Nothing
      else Just $ TermMap $ M.fromList (encodePair <$> M.toList m)
    encodePair (name, classes) = (coreEncodeName name, TermSet $ S.fromList (encodeClass <$> (S.toList classes)))
    encodeClass tc = TermUnion $ Injection _TypeClass $ Field fname $ TermRecord $ Record _UnitType []
      where
        fname = case tc of
          TypeClassEquality -> _TypeClass_equality
          TypeClassOrdering -> _TypeClass_ordering

setTypeDescription :: Y.Maybe String -> Type -> Type
setTypeDescription d = setTypeAnnotation kvDescription (TermLiteral . LiteralString <$> d)

termAnnotation :: Term -> Kv
termAnnotation = aggregateAnnotations $ \t -> case t of
  TermAnnotated a -> Just a
  _ -> Nothing

typeAnnotation :: Type -> Kv
typeAnnotation = aggregateAnnotations $ \t -> case t of
  TypeAnnotated a -> Just a
  _ -> Nothing

whenFlag :: String -> Flow s a -> Flow s a -> Flow s a
whenFlag flag fthen felse = do
  b <- hasFlag flag
  if b
    then fthen
    else felse
