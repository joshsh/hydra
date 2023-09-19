{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier2.Printing where

-- Standard Tier-2 imports
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
import           Hydra.Sources.Tier1.All

import Hydra.Sources.Tier2.Basics


hydraPrintingModule :: Module
hydraPrintingModule = Module (Namespace "hydra/printing") elements [hydraBasicsModule] $
    Just "Utilities for use in transformations"
  where
   elements = [
     el describeFloatTypeDef,
     el describeIntegerTypeDef,
     el describeLiteralTypeDef,
     el describePrecisionDef,
     el describeTypeDef]

printingDefinition :: String -> Datum a -> Definition a
printingDefinition = definitionInModule hydraPrintingModule


describeFloatTypeDef :: Definition (FloatType -> String)
describeFloatTypeDef = printingDefinition "describeFloatType" $
  doc "Display a floating-point type as a string" $
  lambda "t" $ (ref describePrecisionDef <.> ref floatTypePrecisionDef @@ var "t") ++ string " floating-point numbers"

describeIntegerTypeDef :: Definition (IntegerType -> String)
describeIntegerTypeDef = printingDefinition "describeIntegerType" $
  doc "Display an integer type as a string" $
  lambda "t" $ (ref describePrecisionDef <.> ref integerTypePrecisionDef @@ var "t")
    ++ string " integers"

describeLiteralTypeDef :: Definition (LiteralType -> String)
describeLiteralTypeDef = printingDefinition "describeLiteralType" $
  doc "Display a literal type as a string" $
  match _LiteralType Nothing [
    Case _LiteralType_binary  --> constant $ string "binary strings",
    Case _LiteralType_boolean --> constant $ string "boolean values",
    Case _LiteralType_float   --> ref describeFloatTypeDef,
    Case _LiteralType_integer --> ref describeIntegerTypeDef,
    Case _LiteralType_string  --> constant $ string "character strings"]

describePrecisionDef :: Definition (Precision -> String)
describePrecisionDef = printingDefinition "describePrecision" $
  doc "Display numeric precision as a string" $
  match _Precision Nothing [
    Case _Precision_arbitrary --> constant $ string "arbitrary-precision",
    Case _Precision_bits      --> lambda "bits" $ Literals.showInt32 @@ var "bits" ++ string "-bit"]

describeTypeDef :: Definition (Type -> String)
describeTypeDef = printingDefinition "describeType" $
  doc "Display a type as a string" $
  match _Type Nothing [
    Case _Type_annotated   --> lambda "a" $ string "annotated " ++ (ref describeTypeDef @@
      (project _Annotated _Annotated_subject @@ var "a")),
    Case _Type_application --> constant $ string "instances of an application type",
    Case _Type_literal     --> ref describeLiteralTypeDef,
    Case _Type_function    --> lambda "ft" $ string "functions from "
      ++ (ref describeTypeDef @@ (project _FunctionType _FunctionType_domain @@ var "ft"))
      ++ string " to "
      ++ (ref describeTypeDef @@ (project _FunctionType _FunctionType_codomain @@ var "ft")),
    Case _Type_lambda      --> constant $ string "polymorphic terms",
    Case _Type_list        --> lambda "t" $ string "lists of " ++ (ref describeTypeDef @@ var "t"),
    Case _Type_map         --> lambda "mt" $ string "maps from "
      ++ (ref describeTypeDef @@ (project _MapType _MapType_keys @@ var "mt"))
      ++ string " to "
      ++ (ref describeTypeDef @@ (project _MapType _MapType_values  @@ var "mt")),
    Case _Type_optional    --> lambda "ot" $ string "optional " ++ (ref describeTypeDef @@ var "ot"),
    Case _Type_product     --> constant $ string "tuples",
    Case _Type_record      --> constant $ string "records",
    Case _Type_set         --> lambda "st" $ string "sets of " ++ (ref describeTypeDef @@ var "st"),
    Case _Type_stream      --> lambda "t" $ string "streams of " ++ (ref describeTypeDef @@ var "t"),
    Case _Type_sum         --> constant $ string "variant tuples",
    Case _Type_union       --> constant $ string "unions",
    Case _Type_variable    --> constant $ string "instances of a named type",
    Case _Type_wrap        --> lambda "n" $ string "wrapper for "
      ++ (ref describeTypeDef @@ (project _Nominal _Nominal_object @@ var "n"))]
