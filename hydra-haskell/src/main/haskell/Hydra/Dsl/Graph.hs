module Hydra.Dsl.Graph where

import Hydra.Kernel
import Hydra.Dsl.Base as Base

import qualified Data.Map as M


graph :: Datum (M.Map Name (Element a))
    -> Datum (M.Map Name (Maybe (Term a)))
    -> Datum (M.Map Name (Type a))
    -> Datum (Term a)
    -> Datum (M.Map Name (Primitive a))
    -> Datum (AnnotationClass a)
    -> Datum (Maybe (Graph a))
    -> Datum (Graph a)
graph elements environment types body primitives annotations schema = record _Graph [
    _Graph_elements>>: elements,
    _Graph_environment>>: environment,
    _Graph_types>>: types,
    _Graph_body>>: body,
    _Graph_primitives>>: primitives,
    _Graph_annotations>>: annotations,
    _Graph_schema>>: schema]

graphElements :: Datum (Graph a -> M.Map Name (Element a))
graphElements = project _Graph _Graph_elements

graphEnvironment :: Datum (Graph a -> M.Map Name (Maybe (Term a)))
graphEnvironment = project _Graph _Graph_environment

graphTypes :: Datum (Graph a -> M.Map Name (Type a))
graphTypes = project _Graph _Graph_types

graphBody :: Datum (Graph a -> Term a)
graphBody = project _Graph _Graph_body

graphPrimitives :: Datum (Graph a -> M.Map Name (Primitive a))
graphPrimitives = project _Graph _Graph_primitives

graphAnnotations :: Datum (Graph a -> AnnotationClass a)
graphAnnotations = project _Graph _Graph_annotations

graphSchema :: Datum (Graph a -> Maybe (Graph a))
graphSchema = project _Graph _Graph_schema
