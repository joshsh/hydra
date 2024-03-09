-- | Functions for working with annotations

module Hydra.Annotations where

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


annotationKey_classes = "classes" :: String
annotationKey_description = "description" :: String
annotationKey_type = "type" :: String

aggregateAnnotations :: (x -> Maybe (Annotated x)) -> x -> M.Map String Term
aggregateAnnotations getAnn t = M.fromList $ L.concat $ toPairs [] t
  where
    toPairs rest t = case getAnn t of
      Nothing -> rest
      Just (Annotated t' other) -> toPairs ((M.toList other):rest) t'

compressTermAnnotations :: Term -> Term
compressTermAnnotations term = if M.null ann1
    then term1
    else TermAnnotated (Annotated term1 ann1)
  where
    (term1, ann1) = compress term
    compress term = case term of
      TermAnnotated (Annotated subj ann) -> (term2, M.union ann ann2)
        where
          (term2, ann2) = compress subj
      _ -> (term, M.empty)

debug :: String -> Flow Graph ()
debug msg = do
  counter <- nextCount "debugCounter"
  warn ("[" ++ show counter ++ "] " ++ msg) $ pure ()

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

getDescription :: M.Map String Term -> Flow Graph (Y.Maybe String)
getDescription anns = case M.lookup annotationKey_description anns of
  Nothing -> pure Nothing
  Just term -> case term of
    TermLiteral (LiteralString s) -> pure $ Just s
    _ -> fail $ "unexpected value for " ++ show annotationKey_description ++ ": " ++ show term

getTermAnnotation :: String -> Term -> Y.Maybe Term
getTermAnnotation key = M.lookup key . termAnnotation

getTermDescription :: Term -> Flow Graph (Y.Maybe String)
getTermDescription = getDescription . termAnnotation

getTypeAsAnnotation :: M.Map String Term -> Flow Graph (Y.Maybe Type)
getTypeAsAnnotation anns = case M.lookup annotationKey_type anns of
  Nothing -> pure Nothing
  Just dat -> Just <$> coreDecodeType dat

getTypeAnnotation :: String -> Type -> Y.Maybe Term
getTypeAnnotation key = M.lookup key . typeAnnotation

getTypeClasses :: Type -> Flow Graph (M.Map Name (S.Set TypeClass))
getTypeClasses typ = case getTypeAnnotation annotationKey_classes typ of
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
normalizeTermAnnotations term = if M.null anns
    then stripped
    else TermAnnotated $ Annotated stripped anns
  where
    anns = termAnnotation term
    stripped = stripTerm term

normalizeTypeAnnotations :: Type -> Type
normalizeTypeAnnotations typ = if M.null anns
    then stripped
    else TypeAnnotated $ Annotated stripped anns
  where
    anns = typeAnnotation typ
    stripped = stripType typ

putAttr :: String -> Term -> Flow s ()
putAttr key val = Flow q
  where
    q s0 t0 = FlowState (Just ()) s0 (t0 {traceOther = M.insert key val $ traceOther t0})

removeAnnotation :: String -> M.Map String Term -> M.Map String Term
removeAnnotation key = setAnnotation key Nothing

removeType :: M.Map String Term -> M.Map String Term
removeType = removeAnnotation annotationKey_type

setAnnotation :: String -> Y.Maybe Term -> M.Map String Term -> M.Map String Term
setAnnotation key val m = M.alter (const val) key m

setDescription :: Y.Maybe String -> M.Map String Term -> M.Map String Term
setDescription d = setAnnotation annotationKey_description (TermLiteral . LiteralString <$> d)

setTermAnnotation :: String -> Y.Maybe Term -> Term -> Term
setTermAnnotation key val term = if anns == M.empty
    then term'
    else TermAnnotated $ Annotated term' anns
  where
    term' = stripTerm term
    anns = setAnnotation key val $ termAnnotation term

setTermDescription :: Y.Maybe String -> Term -> Term
setTermDescription d = setTermAnnotation annotationKey_description (TermLiteral . LiteralString <$> d)

-- TODO: move me; types are no longer attached using Annotated
setTermType :: Y.Maybe Type -> Term -> Term
setTermType mt term = case term of
 TermAnnotated (Annotated t ann) -> TermAnnotated $ Annotated (setTermType mt t) ann
 TermTyped (TypedTerm _ t) -> setTermType mt t
 _ -> case mt of
   Nothing -> term
   Just t -> TermTyped $ TypedTerm t term

setTypeAsAnnotation :: Y.Maybe Type -> M.Map String Term -> M.Map String Term
setTypeAsAnnotation mt = setAnnotation annotationKey_type (coreEncodeType <$> mt)

setTypeAnnotation :: String -> Y.Maybe Term -> Type -> Type
setTypeAnnotation key val typ = if anns == M.empty
    then typ'
    else TypeAnnotated $ Annotated typ' anns
  where
    typ' = stripType typ
    anns = setAnnotation key val $ typeAnnotation typ

setTypeClasses :: M.Map Name (S.Set TypeClass) -> Type -> Type
setTypeClasses m = setTypeAnnotation annotationKey_classes encoded
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
setTypeDescription d = setTypeAnnotation annotationKey_description (TermLiteral . LiteralString <$> d)

termAnnotation :: Term -> M.Map String Term
termAnnotation = aggregateAnnotations $ \t -> case t of
  TermAnnotated a -> Just a
  _ -> Nothing

typeAnnotation :: Type -> M.Map String Term
typeAnnotation = aggregateAnnotations $ \t -> case t of
  TypeAnnotated a -> Just a
  _ -> Nothing

hasTypeAnnotation :: Term -> Bool
hasTypeAnnotation = M.member annotationKey_type . termAnnotation

whenFlag :: String -> Flow s a -> Flow s a -> Flow s a
whenFlag flag fthen felse = do
  b <- hasFlag flag
  if b
    then fthen
    else felse
