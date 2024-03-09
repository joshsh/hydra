-- | A bootstrapping DSL, used for Hydra's inner core models

module Hydra.Dsl.Bootstrap where

import Hydra.Compute
import Hydra.Constants
import Hydra.Core
import Hydra.CoreEncoding
import Hydra.Graph
import Hydra.Annotations
import Hydra.Module
import Hydra.Rewriting
import Hydra.Sources.Libraries
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types
import Hydra.Tools.Debug

import qualified Data.Map as M
import qualified Data.Set as S


-- | An empty graph (no elements, no primitives, but an annotation class) which is used for bootstrapping Hydra Core
bootstrapGraph :: Graph
bootstrapGraph = Graph {
  graphElements = M.empty,
  graphEnvironment = M.empty,
  graphTypes = M.empty,
  graphBody = Terms.list [], -- Note: the bootstrap body is arbitrary
  graphPrimitives = M.fromList $ fmap (\p -> (primitiveName p, p)) standardPrimitives,
  graphSchema = Nothing}

datatype :: Namespace -> String -> Type -> Element
datatype ns lname typ = typeDefinitionElement elName $ rewriteType replacePlaceholders typ
  where
    elName = qualify ns (Name lname)

    -- Note: placeholders are only expected at the top level, or beneath annotations and/or type lambdas
    replacePlaceholders rec t = case rect of
        TypeRecord (RowType tname e fields) -> if tname == placeholderName
          then TypeRecord (RowType elName e fields)
          else rect
        TypeUnion (RowType tname e fields) -> if tname == placeholderName
          then TypeUnion (RowType elName e fields)
          else rect
        TypeWrap (Nominal tname t) -> if tname == placeholderName
          then TypeWrap (Nominal elName t)
          else rect
        _ -> rect
      where
        rect = rec t

typeref :: Namespace -> String -> Type
typeref ns = TypeVariable . qualify ns . Name

qualify :: Namespace -> Name -> Name
qualify (Namespace ns) (Name lname) = Name $ ns ++ "." ++ lname

typeDefinitionElement :: Name -> Type -> Element
typeDefinitionElement name typ = Element {
    elementName = name,
    elementData = dataTerm}
  where
    -- We annotate the encoded type with the type hydra/core.Type, as the inferred type will actually be the *kind*.
    -- E.g. the inferred type of the Name type is just Type, but the inferred type of the Nominal type is Type -> Type,
    -- as it has a type parameter.
    dataTerm = TermTyped $ TypedTerm (TypeVariable _Type) $ coreEncodeType typ
