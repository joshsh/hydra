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
import Hydra.Mantle
import Hydra.Rewriting
import Hydra.Tier1
import Hydra.Tier2
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


key_classes = "classes" :: String

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
getTermAnnotation key = getAnnotation key . termAnnotationInternal

getTermDescription :: Term -> Flow Graph (Y.Maybe String)
getTermDescription = getDescription . termAnnotationInternal

getType :: Kv -> Flow Graph (Y.Maybe Type)
getType kv = case getAnnotation kvType kv of
  Nothing -> pure Nothing
  Just dat -> Just <$> coreDecodeType dat

getTypeAnnotation :: String -> Type -> Y.Maybe Term
getTypeAnnotation key = getAnnotation key . typeAnnotationInternal

getTypeClasses :: Type -> Flow Graph (M.Map Name (S.Set TypeClass))
getTypeClasses typ = case getTypeAnnotation key_classes typ of
    Nothing -> pure M.empty
    Just term -> Expect.map coreDecodeName (Expect.set decodeClass) term
  where
    decodeClass term = Expect.unitVariant _TypeClass term >>= \fn -> Y.maybe
      (unexpected "type class" $ show term) pure $ M.lookup fn byName
    byName = M.fromList [(_TypeClass_equality, TypeClassEquality), (_TypeClass_ordering, TypeClassOrdering)]

getTypeDescription :: Type -> Flow Graph (Y.Maybe String)
getTypeDescription = getDescription . typeAnnotationInternal

hasFlag :: String -> Flow s Bool
hasFlag flag = getAttrWithDefault flag (Terms.boolean False) >>= Expect.boolean

kvAnnotationClass :: AnnotationClass
kvAnnotationClass = AnnotationClass {
    annotationClassDefault = Kv M.empty,
    annotationClassEqual = (==),
    annotationClassCompare = \m1 m2 -> toComparison $ m1 `compare` m2,
    annotationClassShow = show,
    annotationClassRead = read,

    -- TODO: simplify
    annotationClassTermAnnotation = termAnnotationInternal,
    annotationClassTypeAnnotation = typeAnnotationInternal,
    annotationClassTermDescription = getTermDescription,
    annotationClassTypeDescription = getTypeDescription,
    annotationClassTypeClasses = getTypeClasses,
    annotationClassTermType = getType . termAnnotationInternal,
    annotationClassSetTermDescription = setTermDescription,
    annotationClassSetTermType = setTermType,
    annotationClassSetTypeClasses = setTypeClasses,
    annotationClassTypeOf = getType,
    annotationClassSetTypeOf = setType}
  where
    toComparison c = case c of
      LT -> ComparisonLessThan
      EQ -> ComparisonEqualTo
      GT -> ComparisonGreaterThan

kvDescription :: String
kvDescription = "description"

kvType :: String
kvType = "type"

-- | Return a zero-indexed counter for the given key: 0, 1, 2, ...
nextCount :: String -> Flow s Int
nextCount attrName = do
  count <- getAttrWithDefault attrName (Terms.int32 0) >>= Expect.int32
  putAttr attrName (Terms.int32 $ count + 1)
  return count

resetCount :: String -> Flow s ()
resetCount attrName = do
  putAttr attrName (Terms.int32 0)
  return ()

normalizeTermAnnotations :: Term -> Term
normalizeTermAnnotations term = if M.null (kvAnnotations kv)
    then stripped
    else TermAnnotated $ Annotated stripped kv
  where
    kv = termAnnotationInternal term
    stripped = stripTerm term

normalizeTypeAnnotations :: Type -> Type
normalizeTypeAnnotations typ = if M.null (kvAnnotations kv)
    then stripped
    else TypeAnnotated $ Annotated stripped kv
  where
    kv = typeAnnotationInternal typ
    stripped = stripType typ

putAttr :: String -> Term -> Flow s ()
putAttr key val = Flow q
  where
    q s0 t0 = FlowState (Just ()) s0 (t0 {traceOther = M.insert key val $ traceOther t0})

setAnnotation :: String -> Y.Maybe Term -> Kv -> Kv
setAnnotation key val (Kv m) = Kv $ M.alter (const val) key m

setDescription :: Y.Maybe String -> Kv -> Kv
setDescription d = setAnnotation kvDescription (Terms.string <$> d)

setTermAnnotation :: String -> Y.Maybe Term -> Term -> Term
setTermAnnotation key val term = if kv == Kv M.empty
    then term'
    else TermAnnotated $ Annotated term' kv
  where
    term' = stripTerm term
    kv = setAnnotation key val $ termAnnotationInternal term

setTermDescription :: Y.Maybe String -> Term -> Term
setTermDescription d = setTermAnnotation kvDescription (Terms.string <$> d)

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
    kv = setAnnotation key val $ typeAnnotationInternal typ

setTypeClasses :: M.Map Name (S.Set TypeClass) -> Type -> Type
setTypeClasses m = setTypeAnnotation key_classes encoded
  where
    encoded = if M.null m
      then Nothing
      else Just $ Terms.map $ M.fromList (encodePair <$> M.toList m)
    encodePair (name, classes) = (coreEncodeName name, Terms.set $ S.fromList (encodeClass <$> (S.toList classes)))
    encodeClass tc = Terms.unitVariant _TypeClass $ case tc of
      TypeClassEquality -> _TypeClass_equality
      TypeClassOrdering -> _TypeClass_ordering

setTypeDescription :: Y.Maybe String -> Type -> Type
setTypeDescription d = setTypeAnnotation kvDescription (Terms.string <$> d)

termAnnotationInternal :: Term -> Kv
termAnnotationInternal = aggregateAnnotations $ \t -> case t of
  TermAnnotated a -> Just a
  _ -> Nothing

typeAnnotationInternal :: Type -> Kv
typeAnnotationInternal = aggregateAnnotations $ \t -> case t of
  TypeAnnotated a -> Just a
  _ -> Nothing

whenFlag :: String -> Flow s a -> Flow s a -> Flow s a
whenFlag flag fthen felse = do
  b <- hasFlag flag
  if b
    then fthen
    else felse

-- TODO: move out of Kv and into Rewriting
unshadowVariables :: Term -> Term
unshadowVariables term = Y.fromJust $ flowStateValue $ unFlow (rewriteTermM rewrite (pure . id) term) (S.empty, M.empty) emptyTrace
  where
    rewrite recurse term = do
      (reserved, subst) <- getState
      case term of
        TermVariable v -> pure $ TermVariable $ Y.fromMaybe v $ M.lookup v subst
        TermFunction (FunctionLambda (Lambda v body)) -> if S.member v reserved
          then do
            v' <- freshName
            putState (S.insert v' reserved, M.insert v v' subst)
            body' <- recurse body
            putState (reserved, subst)
            pure $ TermFunction $ FunctionLambda $ Lambda v' body'
          else do
            putState (S.insert v reserved, subst)
            body' <- recurse body
            return $ TermFunction $ FunctionLambda $ Lambda v body'
        _ -> recurse term
    freshName = (\n -> Name $ "s" ++ show n) <$> nextCount "unshadow"
