-- | Basic functions which depend on primitive functions

module Hydra.Extras where

import qualified Hydra.Compute as Compute
import qualified Hydra.Core as Core
import qualified Hydra.Graph as Graph
import qualified Hydra.Lib.Lists as Lists
import qualified Hydra.Lib.Maps as Maps
import qualified Hydra.Lib.Math as Math
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Module as Module
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

functionArity :: (Core.Function a -> Int)
functionArity x = case x of
  Core.FunctionElimination _ -> 1
  Core.FunctionLambda v -> (Math.add 1 (termArity (Core.lambdaBody v)))
  Core.FunctionPrimitive _ -> 42

lookupPrimitive :: (Graph.Graph a -> Core.Name -> Maybe (Graph.Primitive a))
lookupPrimitive g name = (Maps.lookup name (Graph.graphPrimitives g))

-- | Find the arity (expected number of arguments) of a primitive constant or function
primitiveArity :: (Graph.Primitive a -> Int)
primitiveArity x = (typeArity (Graph.primitiveType x))

-- | Construct a qualified (dot-separated) name
qname :: (Module.Namespace -> String -> Core.Name)
qname ns name = (Core.Name (Strings.cat [
  Module.unNamespace ns,
  ".",
  name]))

termArity :: (Core.Term a -> Int)
termArity x = case x of
  Core.TermApplication v -> ((\x -> Math.sub x 1) (termArity (Core.applicationFunction v)))
  Core.TermFunction v -> (functionArity v)
  _ -> 0

typeArity :: (Core.Type a -> Int)
typeArity x = case x of
  Core.TypeAnnotated v -> (typeArity (Core.annotatedSubject v))
  Core.TypeApplication v -> (typeArity (Core.applicationTypeFunction v))
  Core.TypeLambda v -> (typeArity (Core.lambdaTypeBody v))
  Core.TypeFunction v -> (Math.add 1 (typeArity (Core.functionTypeCodomain v)))
  _ -> 0

-- | Uncurry a type expression into a list of types, turning a function type a -> b into cons a (uncurryType b)
uncurryType :: (Core.Type a -> [Core.Type a])
uncurryType t = ((\x -> case x of
  Core.TypeAnnotated v -> (uncurryType (Core.annotatedSubject v))
  Core.TypeApplication v -> (uncurryType (Core.applicationTypeFunction v))
  Core.TypeLambda v -> (uncurryType (Core.lambdaTypeBody v))
  Core.TypeFunction v -> (Lists.cons (Core.functionTypeDomain v) (uncurryType (Core.functionTypeCodomain v)))
  _ -> [
    t]) t)

emptyKv :: (Compute.Kv)
emptyKv = Compute.Kv {
  Compute.kvAnnotations = Maps.empty}

getAnnotation :: (String -> Compute.Kv -> Maybe (Core.Term Compute.Kv))
getAnnotation key ann = (Maps.lookup key (Compute.kvAnnotations ann))