-- | A DSL which is used as a basis for some of the other DSLs

module Hydra.Dsl.Annotations where

import Hydra.Core
import Hydra.Compute
import Hydra.Kv
import Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Data.Map as M
import qualified Data.Maybe as Y


key_maxSize = "maxLength"
key_minSize = "minLength"

annotateTerm :: String -> Y.Maybe Term -> Term -> Term
annotateTerm = setTermAnnotation

annotateType :: String -> Y.Maybe Term -> Type -> Type
annotateType = setTypeAnnotation

bounded :: Maybe Int -> Maybe Int -> Type -> Type
bounded min max = annotMin . annotMax
  where
    annotMax t = Y.maybe t (`setMaxLength` t) max
    annotMin t = Y.maybe t (`setMinLength` t) max

boundedList :: Maybe Int -> Maybe Int -> Type -> Type
boundedList min max et = bounded min max $ Types.list et

boundedSet :: Maybe Int -> Maybe Int -> Type -> Type
boundedSet min max et = bounded min max $ Types.set et

boundedString :: Maybe Int -> Maybe Int -> Type
boundedString min max = bounded min max Types.string

doc :: String -> Type -> Type
doc s = setTypeDescription (Just s)

dataDoc :: String -> Term -> Term
dataDoc s = setTermDescription (Just s)

nonemptyList :: Type -> Type
nonemptyList = boundedList (Just 1) Nothing

note :: String -> Type -> Type
note s = doc $ "Note: " ++ s

see :: String -> Type -> Type
see s = doc $ "See " ++ s

setMaxLength :: Int -> Type -> Type
setMaxLength m = setTypeAnnotation key_maxSize (Just $ Terms.int32 m)

setMinLength :: Int -> Type -> Type
setMinLength m = setTypeAnnotation key_minSize (Just $ Terms.int32 m)

twoOrMoreList :: Type -> Type
twoOrMoreList = boundedList (Just 2) Nothing
