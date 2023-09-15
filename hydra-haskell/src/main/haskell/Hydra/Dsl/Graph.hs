module Hydra.Dsl.Graph where

import Hydra.Kernel
import Hydra.Dsl.Base as Base

import qualified Data.Map as M


graph :: Datum (M.Map Name (Element Kv))
    -> Datum (M.Map Name (Maybe (Term Kv)))
    -> Datum (M.Map Name (Type Kv))
    -> Datum (Term Kv)
    -> Datum (M.Map Name (Primitive Kv))
    -> Datum (AnnotationClass Kv)
    -> Datum (Maybe (Graph Kv))
    -> Datum (Graph Kv)
graph elements environment types body primitives annotations schema = record _Graph [
    _Graph_elements>>: elements,
    _Graph_environment>>: environment,
    _Graph_types>>: types,
    _Graph_body>>: body,
    _Graph_primitives>>: primitives,
    _Graph_annotations>>: annotations,
    _Graph_schema>>: schema]

graphElements :: Datum (Graph Kv -> M.Map Name (Element Kv))
graphElements = project _Graph _Graph_elements

graphEnvironment :: Datum (Graph Kv -> M.Map Name (Maybe (Term Kv)))
graphEnvironment = project _Graph _Graph_environment

graphTypes :: Datum (Graph Kv -> M.Map Name (Type Kv))
graphTypes = project _Graph _Graph_types

graphBody :: Datum (Graph Kv -> Term Kv)
graphBody = project _Graph _Graph_body

graphPrimitives :: Datum (Graph Kv -> M.Map Name (Primitive Kv))
graphPrimitives = project _Graph _Graph_primitives

graphAnnotations :: Datum (Graph Kv -> AnnotationClass Kv)
graphAnnotations = project _Graph _Graph_annotations

graphSchema :: Datum (Graph Kv -> Maybe (Graph Kv))
graphSchema = project _Graph _Graph_schema
