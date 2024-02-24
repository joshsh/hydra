module Hydra.Sources.Tier1.Strip where

-- Standard Tier-1 imports
import           Prelude hiding ((++))
import qualified Data.List                 as L
import qualified Data.Map                  as M
import qualified Data.Set                  as S
import qualified Data.Maybe                as Y
import           Hydra.Dsl.Base            as Base
import qualified Hydra.Dsl.Core            as Core
import qualified Hydra.Dsl.Graph           as Graph
import qualified Hydra.Dsl.Lib.Equality    as Equality
import qualified Hydra.Dsl.Lib.Flows       as Flows
import qualified Hydra.Dsl.Lib.Io          as Io
import qualified Hydra.Dsl.Lib.Lists       as Lists
import qualified Hydra.Dsl.Lib.Literals    as Literals
import qualified Hydra.Dsl.Lib.Logic       as Logic
import qualified Hydra.Dsl.Lib.Maps        as Maps
import qualified Hydra.Dsl.Lib.Math        as Math
import qualified Hydra.Dsl.Lib.Optionals   as Optionals
import qualified Hydra.Dsl.Lib.Sets        as Sets
import           Hydra.Dsl.Lib.Strings     as Strings
import qualified Hydra.Dsl.Module          as Module
import qualified Hydra.Dsl.Terms           as Terms
import qualified Hydra.Dsl.Types           as Types
import           Hydra.Sources.Tier0.All


stripDefinition :: String -> Datum a -> Definition a
stripDefinition = definitionInModule hydraStripModule

hydraStripModule :: Module
hydraStripModule = Module (Namespace "hydra/strip") elements [hydraCoreModule] $
    Just "Several functions for stripping annotations from types and terms."
  where
   elements = [
     el skipAnnotationsDef,
     el stripTermDef,
     el stripTypeDef,
     el stripTypeParametersDef]

skipAnnotationsDef :: Definition ((a -> Maybe (Annotated a)) -> a -> a)
skipAnnotationsDef = stripDefinition "skipAnnotations" $
  function getAnnType (funT aT aT) $
  lambda "getAnn" $ lambda "t" $
    (var "skip" @@ var "t") `with` [
      "skip">:
        function (Types.var "x") (Types.var "x") $
        lambda "t1" $
          (matchOpt
            (var "t1")
            (lambda "ann" $ var "skip" @@ (project _Annotated _Annotated_subject @@ var "ann")))
          @@ (var "getAnn" @@ var "t1")]
  where
    getAnnType = (funT aT (optionalT $ annotatedT aT))

stripTermDef :: Definition (Term -> Term)
stripTermDef = stripDefinition "stripTerm" $
  doc "Strip all annotations from a term" $
  function termT termT $
  lambda "x" $ (match _Term (Just $ var "x") [
    Case _Term_typed --> lambda "tt" $ ref stripTermDef @@ (project _TypedTerm _TypedTerm_term @@ var "tt"),
    Case _Term_annotated --> lambda "at" $ ref stripTermDef @@ (project _Annotated _Annotated_subject @@ var "at")]) @@ var "x"

stripTypeDef :: Definition (Type -> Type)
stripTypeDef = stripDefinition "stripType" $
  doc "Strip all annotations from a type" $
  function typeT typeT $
  lambda "x" (ref skipAnnotationsDef @@ (match _Type (Just nothing) [
    Case _Type_annotated --> lambda "ann" (just $ var "ann")]) @@ var "x")

stripTypeParametersDef :: Definition (Type -> Type)
stripTypeParametersDef = stripDefinition "stripTypeParameters" $
    doc "Strip any top-level type lambdas from a type, extracting the (possibly nested) type body" $
    function typeT typeT $
      lambda "t" $ match _Type (Just $ var "t") [
        Case _Type_lambda --> lambda "lt" (ref stripTypeParametersDef @@ (project _LambdaType _LambdaType_body @@ var "lt"))
        ] @@ (ref stripTypeDef @@ var "t")
