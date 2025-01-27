-- | A DSL which is used as a basis for some of the other DSLs

module Hydra.Dsl.Annotations where

import Hydra.Core
import Hydra.Compute
import Hydra.Annotations
import Hydra.Tools.Formatting
import Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Data.Map as M
import qualified Data.Maybe as Y


key_deprecated = Name "_deprecated"
key_exclude = Name "exclude"
key_maxLength = Name "_maxLength"
key_minLength = Name "_minLength"
key_preserveFieldName = Name "_preserveFieldName"


annotateTerm :: Name -> Y.Maybe Term -> Term -> Term
annotateTerm = setTermAnnotation

annotateType :: Name -> Y.Maybe Term -> Type -> Type
annotateType = setTypeAnnotation

bounded :: Maybe Int -> Maybe Int -> Type -> Type
bounded min max = annotMin . annotMax
  where
    annotMax t = Y.maybe t (`setMaxLength` t) max
    annotMin t = Y.maybe t (`setMinLength` t) max

boundedList :: Maybe Int -> Maybe Int -> Type -> Type
boundedList min max et = bounded min max $ Types.list et

boundedMap :: Maybe Int -> Maybe Int -> Type -> Type -> Type
boundedMap min max kt vt = bounded min max $ Types.map kt vt

boundedSet :: Maybe Int -> Maybe Int -> Type -> Type
boundedSet min max et = bounded min max $ Types.set et

boundedString :: Maybe Int -> Maybe Int -> Type
boundedString min max = bounded min max Types.string

deprecated :: Type -> Type
deprecated = setTypeAnnotation key_deprecated (Just $ Terms.boolean True)

doc :: String -> Type -> Type
doc s = setTypeDescription (Just s)

doc70 :: String -> Type -> Type
doc70 = doc . wrapLine 70

doc80 :: String -> Type -> Type
doc80 = doc . wrapLine 80

dataDoc :: String -> Term -> Term
dataDoc s = setTermDescription (Just s)

exclude :: Type -> Type
exclude = setTypeAnnotation key_exclude $ Just $ Terms.boolean True

minLengthList :: Int -> Type -> Type
minLengthList len = boundedList (Just len) Nothing

nonemptyList :: Type -> Type
nonemptyList = minLengthList 1

nonemptyMap :: Type -> Type -> Type
nonemptyMap = boundedMap (Just 1) Nothing

note :: String -> Type -> Type
note s = doc $ "Note: " ++ s

preserveFieldName :: Type -> Type
preserveFieldName = setTypeAnnotation key_preserveFieldName (Just $ Terms.boolean True)

see :: String -> Type -> Type
see s = doc $ "See " ++ s

setMaxLength :: Int -> Type -> Type
setMaxLength m = setTypeAnnotation key_maxLength (Just $ Terms.int32 m)

setMinLength :: Int -> Type -> Type
setMinLength m = setTypeAnnotation key_minLength (Just $ Terms.int32 m)

twoOrMoreList :: Type -> Type
twoOrMoreList = boundedList (Just 2) Nothing
