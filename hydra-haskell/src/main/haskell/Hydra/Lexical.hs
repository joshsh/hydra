-- | Functions for retrieving elements and primitive functions from a graph context

module Hydra.Lexical where

import Hydra.Basics
import Hydra.Strip
import Hydra.Core
import Hydra.Extras
import Hydra.Graph
import Hydra.Compute
import Hydra.Tier1
import Hydra.Tier2

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as Y
import Control.Monad


dereferenceElement :: Name -> Flow Graph (Maybe (Element))
dereferenceElement name = do
  g <- getState
  return $ M.lookup name (graphElements g)

requireElement :: Name -> Flow Graph (Element)
requireElement name = do
    mel <- dereferenceElement name
    case mel of
      Just el -> return el
      Nothing -> getState >>= err
  where
    err g = fail $ "no such element: " ++ unName name
        ++ ". Available elements: {" ++ L.intercalate ", " (ellipsis (unName . elementName <$> M.elems (graphElements g))) ++ "}"
      where
        showAll = False
        ellipsis strings = if L.length strings > 3 && not showAll
          then L.take 3 strings ++ ["..."]
          else strings

requirePrimitive :: Name -> Flow Graph (Primitive)
requirePrimitive fn = do
    cx <- getState
    Y.maybe err pure $ lookupPrimitive cx fn
  where
    err = fail $ "no such primitive function: " ++ unName fn

-- TODO: distinguish between lambda-bound and let-bound variables
resolveTerm :: Name -> Flow Graph (Maybe Term)
resolveTerm name = do
    g <- getState
    Y.maybe (pure Nothing) recurse $ M.lookup name $ graphElements g
  where
    recurse el = case stripTerm (elementData el) of
      TermVariable name' -> resolveTerm name'
      _ -> pure $ Just $ elementData el

-- Note: assuming for now that primitive functions are the same in the schema graph
schemaContext :: Graph -> Graph
schemaContext g = Y.fromMaybe g (graphSchema g)

withSchemaContext :: Flow Graph x -> Flow Graph x
withSchemaContext f = do
  cx <- getState
  withState (schemaContext cx) f
