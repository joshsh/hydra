module Hydra.Dsl.Graph where

import Hydra.Kernel
import Hydra.Dsl.Base as Base

import qualified Data.Map as M


graph :: Datum (M.Map Name (Element))
    -> Datum (M.Map Name (Maybe Term))
    -> Datum (M.Map Name Type)
    -> Datum Term
    -> Datum (M.Map Name (Primitive))
    -> Datum (AnnotationClass)
    -> Datum (Maybe Graph)
    -> Datum Graph
graph elements environment types body primitives annotations schema = record _Graph [
    _Graph_elements>>: elements,
    _Graph_environment>>: environment,
    _Graph_types>>: types,
    _Graph_body>>: body,
    _Graph_primitives>>: primitives,
    _Graph_annotations>>: annotations,
    _Graph_schema>>: schema]

graphElements :: Datum (Graph -> M.Map Name (Element))
graphElements = project _Graph _Graph_elements

graphEnvironment :: Datum (Graph -> M.Map Name (Maybe Term))
graphEnvironment = project _Graph _Graph_environment

graphTypes :: Datum (Graph -> M.Map Name Type)
graphTypes = project _Graph _Graph_types

graphBody :: Datum (Graph -> Term)
graphBody = project _Graph _Graph_body

graphPrimitives :: Datum (Graph -> M.Map Name (Primitive))
graphPrimitives = project _Graph _Graph_primitives

graphAnnotations :: Datum (Graph -> AnnotationClass)
graphAnnotations = project _Graph _Graph_annotations

graphSchema :: Datum (Graph -> Maybe Graph)
graphSchema = project _Graph _Graph_schema
