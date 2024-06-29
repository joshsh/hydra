-- | The extension to graphs of Hydra's core type system (hydra/core)

module Hydra.Graph where

import qualified Hydra.Compute as Compute
import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | An equality judgement: less than, equal to, or greater than
data Comparison = 
  ComparisonLessThan  |
  ComparisonEqualTo  |
  ComparisonGreaterThan 
  deriving (Eq, Ord, Read, Show)

_Comparison = (Core.Name "hydra/graph.Comparison")

_Comparison_lessThan = (Core.Name "lessThan")

_Comparison_equalTo = (Core.Name "equalTo")

_Comparison_greaterThan = (Core.Name "greaterThan")

-- | A graph, or set of name/term bindings together with parameters (annotations, primitives) and a schema graph
data Graph = 
  Graph {
    -- | All of the elements in the graph
    graphElements :: (Map Core.Name Element),
    -- | The lambda environment of this graph context; it indicates whether a variable is bound by a lambda (Nothing) or a let (Just term)
    graphEnvironment :: (Map Core.Name (Maybe Core.Term)),
    -- | The typing environment of the graph, i.e. the types to which term variables are bound
    graphTypes :: (Map Core.Name Core.Type),
    -- | The body of the term which generated this context
    graphBody :: Core.Term,
    -- | All supported primitive constants and functions, by name
    graphPrimitives :: (Map Core.Name Primitive),
    -- | The schema of this graph. If this parameter is omitted (nothing), the graph is its own schema graph.
    graphSchema :: (Maybe Graph)}

_Graph = (Core.Name "hydra/graph.Graph")

_Graph_elements = (Core.Name "elements")

_Graph_environment = (Core.Name "environment")

_Graph_types = (Core.Name "types")

_Graph_body = (Core.Name "body")

_Graph_primitives = (Core.Name "primitives")

_Graph_annotations = (Core.Name "annotations")

_Graph_schema = (Core.Name "schema")

-- | A graph element, having a name, data term (value), and schema term (type)
data Element = 
  Element {
    elementName :: Core.Name,
    elementData :: Core.Term}
  deriving (Eq, Ord, Read, Show)

_Element = (Core.Name "hydra/graph.Element")

_Element_name = (Core.Name "name")

_Element_data = (Core.Name "data")

-- | A built-in function
data Primitive = 
  Primitive {
    -- | The unique name of the primitive function
    primitiveName :: Core.Name,
    -- | The type signature of the primitive function
    primitiveType :: Core.Type,
    -- | A concrete implementation of the primitive function
    primitiveImplementation :: ([Core.Term] -> Compute.Flow Graph Core.Term)}

_Primitive = (Core.Name "hydra/graph.Primitive")

_Primitive_name = (Core.Name "name")

_Primitive_type = (Core.Name "type")

_Primitive_implementation = (Core.Name "implementation")

-- | A type together with a coder for mapping terms into arguments for primitive functions, and mapping computed results into terms
data TermCoder a = 
  TermCoder {
    termCoderType :: Core.Type,
    termCoderCoder :: (Compute.Coder Graph Graph Core.Term a)}

_TermCoder = (Core.Name "hydra/graph.TermCoder")

_TermCoder_type = (Core.Name "type")

_TermCoder_coder = (Core.Name "coder")

-- | Any of a small number of built-in type classes
data TypeClass = 
  TypeClassEquality  |
  TypeClassOrdering 
  deriving (Eq, Ord, Read, Show)

_TypeClass = (Core.Name "hydra/graph.TypeClass")

_TypeClass_equality = (Core.Name "equality")

_TypeClass_ordering = (Core.Name "ordering")
