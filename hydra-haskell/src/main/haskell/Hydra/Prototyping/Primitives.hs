module Hydra.Prototyping.Primitives (
  graphElementsMap,
  lookupPrimitiveFunction,
  primitiveFunctionArity,
  requireElement,
  requirePrimitiveFunction,
  schemaContext,
) where

import Hydra.Core
import Hydra.Evaluation
import Hydra.Graph
import Hydra.Prototyping.Steps

import qualified Data.Map as M
import qualified Data.Maybe as Y


getGraph :: GraphSet -> GraphName -> Result Graph
getGraph graphs name = Y.maybe error pure $ M.lookup name (graphSetGraphs graphs)
  where
    error = fail $ "no such graph: " ++ name

graphElementsMap :: Graph -> M.Map Name Element
graphElementsMap g = M.fromList $ (\e -> (elementName e , e)) <$> graphElements g

lookupPrimitiveFunction :: Context -> Name -> Maybe PrimitiveFunction
lookupPrimitiveFunction context fn = M.lookup fn $ contextFunctions context

primitiveFunctionArity :: PrimitiveFunction -> Int
primitiveFunctionArity = arity . primitiveFunctionType
  where
    arity (FunctionType _ cod) = 1 + case cod of
      TypeFunction ft -> arity ft
      _ -> 0

requireElement :: Context -> Name -> Result Element
requireElement context name = Y.maybe error pure $ M.lookup name $ contextElements context
  where
    error = fail $ "no such element: " ++ name
      ++ " in graph " ++ graphSetRoot (contextGraphs context)

requirePrimitiveFunction :: Context -> Name -> Result PrimitiveFunction
requirePrimitiveFunction context fn = Y.maybe error pure $ lookupPrimitiveFunction context fn
  where
    error = fail $ "no such primitive function: " ++ fn

schemaContext :: Context -> Result Context
schemaContext context = do
    dgraph <- getGraph graphs $ graphSetRoot graphs
    sgraph <- getGraph graphs $ graphSchemaGraph dgraph
    -- Note: assuming for now that primitive functions and evaluation strategy are the same in the schema graph
    return context {
      contextGraphs = graphs { graphSetRoot = graphName sgraph },
      contextElements = graphElementsMap sgraph}
  where
    graphs = contextGraphs context
