{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier1.Tier1 where

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

import Hydra.Sources.Tier1.Constants
import Hydra.Sources.Tier1.Strip


tier1Definition :: String -> Datum a -> Definition a
tier1Definition = definitionInModule hydraTier1Module

hydraTier1Module :: Module
hydraTier1Module = Module (Namespace "hydra/tier1") elements
    [hydraStripModule] $
--    [hydraGraphModule, hydraMantleModule, hydraComputeModule, hydraStripModule, hydraConstantsModule] $
    Just ("A module for miscellaneous tier-1 functions and constants.")
  where
   elements = [
--     el floatValueToBigfloatDef,
--     el integerValueToBigintDef,
--     el isLambdaDef,
--     el unqualifyNameDef,
--     -- Rewriting.hs
--     el foldOverTermDef,
--     el foldOverTypeDef,
--     el freeVariablesInTermDef,
--     el freeVariablesInTypeDef,
--     el subtermsDef,
     el subtypesDef
--     -- Flows.hs
--     el emptyTraceDef,
--     el flowSucceedsDef,
--     el fromFlowDef,
--     el mutateTraceDef,
--     el pushErrorDef,
--     el warnDef,
--     el withFlagDef,
--     el withStateDef,
--     el withTraceDef
     ]

floatValueToBigfloatDef :: Definition (FloatValue -> Double)
floatValueToBigfloatDef = tier1Definition "floatValueToBigfloat" $
  doc "Convert a floating-point value of any precision to a bigfloat" $
  match _FloatValue Nothing [
    _FloatValue_bigfloat>>: Equality.identity,
    _FloatValue_float32>>: Literals.float32ToBigfloat,
    _FloatValue_float64>>: Literals.float64ToBigfloat]

integerValueToBigintDef :: Definition (IntegerValue -> Integer)
integerValueToBigintDef = tier1Definition "integerValueToBigint" $
  doc "Convert an integer value of any precision to a bigint" $
  match _IntegerValue Nothing [
    _IntegerValue_bigint>>: Equality.identity,
    _IntegerValue_int8>>: Literals.int8ToBigint,
    _IntegerValue_int16>>: Literals.int16ToBigint,
    _IntegerValue_int32>>: Literals.int32ToBigint,
    _IntegerValue_int64>>: Literals.int64ToBigint,
    _IntegerValue_uint8>>: Literals.uint8ToBigint,
    _IntegerValue_uint16>>: Literals.uint16ToBigint,
    _IntegerValue_uint32>>: Literals.uint32ToBigint,
    _IntegerValue_uint64>>: Literals.uint64ToBigint]

isLambdaDef :: Definition (Term -> Bool)
isLambdaDef = tier1Definition "isLambda" $
  doc "Check whether a term is a lambda, possibly nested within let and/or annotation terms" $
  function termT Types.boolean $
  lambda "term" $ (match _Term (Just false) [
      _Term_function>>: match _Function (Just false) [
        _Function_lambda>>: constant true],
      _Term_let>>: lambda "lt" (ref isLambdaDef @@ (project _Let _Let_environment @@ var "lt"))])
    @@ (ref stripTermDef @@ var "term")

-- Rewriting.hs

foldOverTermDef :: Definition (TraversalOrder -> (x -> Term -> x) -> x -> Term -> x)
foldOverTermDef = tier1Definition "foldOverTerm" $
  doc "Fold over a term, traversing its subterms in the specified order" $
  functionN [TypeVariable _TraversalOrder, funT xT (funT termT xT), xT, termT, xT] $
  lambda "order" $ lambda "fld" $ lambda "b0" $ lambda "term" $ (match _TraversalOrder Nothing [
    _TraversalOrder_pre>>: constant (Base.fold (ref foldOverTermDef @@ var "order" @@ var "fld")
      @@ (var "fld" @@ var "b0" @@ var "term")
      @@ (ref subtermsDef @@ var "term")),
    _TraversalOrder_post>>: constant (var "fld"
      @@ (Base.fold (ref foldOverTermDef @@ var "order" @@ var "fld")
        @@ (var "b0")
        @@ (ref subtermsDef @@ var "term"))
      @@ var "term")] @@ var "order")

foldOverTypeDef :: Definition (TraversalOrder -> (x -> Type -> x) -> x -> Type -> x)
foldOverTypeDef = tier1Definition "foldOverType" $
  doc "Fold over a type, traversing its subtypes in the specified order" $
  functionN [TypeVariable _TraversalOrder, funT xT (funT typeT xT), xT, typeT, xT] $
  lambda "order" $ lambda "fld" $ lambda "b0" $ lambda "typ" $ (match _TraversalOrder Nothing [
    _TraversalOrder_pre>>: constant (Base.fold (ref foldOverTypeDef @@ var "order" @@ var "fld")
      @@ (var "fld" @@ var "b0" @@ var "typ")
      @@ (ref subtypesDef @@ var "typ")),
    _TraversalOrder_post>>: constant (var "fld"
      @@ (Base.fold (ref foldOverTypeDef @@ var "order" @@ var "fld")
        @@ (var "b0")
        @@ (ref subtypesDef @@ var "typ"))
      @@ var "typ")] @@ var "order")

freeVariablesInTermDef :: Definition (Term -> S.Set Name)
freeVariablesInTermDef = tier1Definition "freeVariablesInTerm" $
  doc "Find the free variables (i.e. variables not bound by a lambda or let) in a given term" $
  function termT (setT nameT) $
  lambda "term" (
    (match _Term (Just $ var "dfltVars") [
      _Term_function>>: match _Function (Just $ var "dfltVars") [
        _Function_lambda>>: lambda "l" (Sets.remove
          @@ (Core.lambdaParameter @@ var "l")
          @@ (ref freeVariablesInTermDef @@ (Core.lambdaBody @@ var "l")))],
--      TODO: restore the following
--      _Term_let>>: lambda "l" (Sets.difference
--        @@ (ref freeVariablesInTermDef @@ (Core.letEnvironment @@ var "l"))
--        @@ (Sets.fromList @@ (Lists.map @@ first @@ (Maps.toList @@ (Core.letBindings @@ var "l"))))),
      _Term_variable>>: lambda "v" (Sets.singleton @@ var "v")] @@ var "term")
    `with` [
      "dfltVars">: typed (setT nameT) $ Base.fold (lambda "s" $ lambda "t" $ Sets.union @@ var "s" @@ (ref freeVariablesInTermDef @@ var "t"))
        @@ Sets.empty
        @@ (ref subtermsDef @@ var "term")])

freeVariablesInTypeDef :: Definition (Type -> S.Set Name)
freeVariablesInTypeDef = tier1Definition "freeVariablesInType" $
  doc "Find the free variables (i.e. variables not bound by a lambda/universal type) in a given type" $
  function typeT (setT nameT) $
  lambda "typ" (
    (match _Type (Just $ var "dfltVars") [
      _Type_lambda>>: lambda "lt" (Sets.remove
          @@ (Core.lambdaTypeParameter @@ var "lt")
          @@ (ref freeVariablesInTypeDef @@ (Core.lambdaTypeBody @@ var "lt"))),
      -- TODO: let-types
      _Type_variable>>: lambda "v" (Sets.singleton @@ var "v")] @@ var "typ")
    `with` [
      "dfltVars">: typed (setT nameT) $ Base.fold (lambda "s" $ lambda "t" $ Sets.union @@ var "s" @@ (ref freeVariablesInTypeDef @@ var "t"))
        @@ Sets.empty
        @@ (ref subtypesDef @@ var "typ")])

subtermsDef :: Definition (Term -> [Term])
subtermsDef = tier1Definition "subterms" $
  doc "Find the children of a given term" $
--  function termT (listT termT) $
  match _Term Nothing [
    _Term_annotated>>: lambda "at" $ list [Core.annotatedSubject @@ var "at"],
    _Term_application>>: lambda "p" $ list [
      Core.applicationFunction @@ var "p",
      Core.applicationArgument @@ var "p"],
    _Term_function>>: match _Function (Just $ list []) [
        _Function_elimination>>: match _Elimination (Just $ list []) [
            _Elimination_list>>: lambda "fld" $ list [var "fld"],
            _Elimination_optional>>: lambda "oc" $ list [
              Core.optionalCasesNothing @@ var "oc",
              Core.optionalCasesJust @@ var "oc"],
            _Elimination_union>>: lambda "cs" $ Lists.concat2
              @@ ((matchOpt (list []) (lambda "t" $ list [var "t"])) @@ (Core.caseStatementDefault @@ var "cs"))
              @@ (Lists.map @@ Core.fieldTerm @@ (Core.caseStatementCases @@ var "cs"))],
        _Function_lambda>>: lambda "l" $ list [Core.lambdaBody @@ var "l"]],
    _Term_let>>: lambda "lt" $ Lists.cons
      @@ (Core.letEnvironment @@ var "lt")
      @@ (Lists.map @@ second @@ (Maps.toList @@ (Core.letBindings @@ var "lt"))),
    _Term_list>>: lambda "l" $ var "l",
    _Term_literal>>: constant $ list [],
    _Term_map>>: lambda "m" (Lists.concat @@
      (Lists.map @@ (lambda "p" $ list [first @@ var "p", second @@ var "p"]) @@ (Maps.toList @@ var "m"))),
    _Term_optional>>: matchOpt (list []) (lambda "t" $ list [var "t"]),
    _Term_product>>: lambda "tuple" $ var "tuple",
    _Term_record>>: lambda "rt" (Lists.map @@ Core.fieldTerm @@ (Core.recordFields @@ var "rt")),
    _Term_set>>: Sets.toList,
    _Term_stream>>: constant $ list [],
    _Term_sum>>: lambda "st" $ list [Core.sumTerm @@ var "st"],
    _Term_union>>: lambda "ut" $ list [Core.fieldTerm @@ (Core.injectionField @@ var "ut")],
    _Term_variable>>: constant $ list [],
    _Term_wrap>>: lambda "n" $ list [Core.nominalObject @@ var "n"]]

--subtypesDef :: Definition (Type -> [Type])
--subtypesDef = tier1Definition "subtypes" $
--  doc "Find the children of a given type expression" $
----  function typeT (listT typeT) $
--  match _Type Nothing [
--    _Type_annotated>>: lambda "at" $ list [Core.annotatedSubject @@ var "at"],
--    _Type_application>>: lambda "at" $ list [
--      Core.applicationTypeFunction @@ var "at",
--      Core.applicationTypeArgument @@ var "at"],
--    _Type_function>>: lambda "ft" $ list [
--      Core.functionTypeDomain @@ var "ft",
--      Core.functionTypeCodomain @@ var "ft"],
--    _Type_lambda>>: lambda "lt" $ list [Core.lambdaTypeBody @@ var "lt"],
--    _Type_list>>: lambda "lt" $ list [var "lt"],
--    _Type_literal>>: constant $ list [],
--    _Type_map>>: lambda "mt" $ list [
--      Core.mapTypeKeys @@ var "mt",
--      Core.mapTypeValues @@ var "mt"],
--    _Type_optional>>: lambda "ot" $ list [var "ot"],
--    _Type_product>>: lambda "pt" $ var "pt",
--    _Type_record>>: lambda "rt" (Lists.map @@ Core.fieldTypeType @@ (Core.rowTypeFields @@ var "rt")),
--    _Type_set>>: lambda "st" $ list [var "st"],
--    _Type_stream>>: lambda "st" $ list [var "st"],
--    _Type_sum>>: lambda "st" $ var "st",
--    _Type_union>>: lambda "rt" (Lists.map @@ Core.fieldTypeType @@ (Core.rowTypeFields @@ var "rt")),
--    _Type_variable>>: constant $ list [],
--    _Type_wrap>>: lambda "nt" $ list [Core.nominalObject @@ var "nt"]]




subtypesDef :: Definition (Type -> [Type])
subtypesDef = tier1Definition "subtypes" $
  match (Name "hydra/core.Type") (Just $ list []) [
--    _Type_annotated>>: lambda "at" $ list [Core.annotatedSubject @@ var "at"],
--    _Type_application>>: lambda "at" $ list [
--      Core.applicationTypeFunction @@ var "at",
--      Core.applicationTypeArgument @@ var "at"],
--    _Type_function>>: lambda "ft" $ list [
--      Core.functionTypeDomain @@ var "ft",
--      Core.functionTypeCodomain @@ var "ft"],
--    _Type_lambda>>: lambda "lt" $ list [Core.lambdaTypeBody @@ var "lt"],
--    _Type_list>>: lambda "lt" $ list [var "lt"],
--    _Type_literal>>: constant $ list []
--    _Type_map>>: lambda "mt" $ list [
--      Core.mapTypeKeys @@ var "mt",
--      Core.mapTypeValues @@ var "mt"],
--    _Type_optional>>: lambda "ot" $ list [var "ot"],
--    _Type_product>>: lambda "pt" $ var "pt",
--    _Type_record>>: lambda "rt" (Lists.map @@ Core.fieldTypeType @@ (Core.rowTypeFields @@ var "rt")),
--    _Type_set>>: lambda "st" $ list [var "st"],
--    _Type_stream>>: lambda "st" $ list [var "st"],
--    _Type_sum>>: lambda "st" $ var "st",
--    _Type_union>>: lambda "rt" (Lists.map @@ Core.fieldTypeType @@ (Core.rowTypeFields @@ var "rt")),
--    _Type_variable>>: constant $ list [],
--    _Type_wrap>>: lambda "nt" $ list [Core.nominalObject @@ var "nt"]
    ]






unqualifyNameDef :: Definition (QualifiedName -> Name)
unqualifyNameDef = tier1Definition "unqualifyName" $
  doc "Convert a qualified name to a dot-separated name" $
  lambda "qname" $ (wrap _Name $ var "prefix" ++ (project _QualifiedName _QualifiedName_local @@ var "qname"))
    `with` [
      "prefix">: matchOpt (string "") (lambda "n" $ (unwrap _Namespace @@ var "n") ++ string ".")
        @@ (project _QualifiedName _QualifiedName_namespace @@ var "qname")]

-- Flows.hs

emptyTraceDef :: Definition Trace
emptyTraceDef = tier1Definition "emptyTrace" $
  record _Trace [
    _Trace_stack>>: list [],
    _Trace_messages>>: list [],
    _Trace_other>>: Maps.empty]

flowSucceedsDef :: Definition (s -> Flow s a -> Bool)
flowSucceedsDef = tier1Definition "flowSucceeds" $
  doc "Check whether a flow succeeds" $
--  typed (Types.lambdas ["s", "a"] $ Types.functionN [sT, flowSA, booleanT]) $
  functionN [sT, flowSA, booleanT] $
  lambda "state" $ lambda "f" $
    Optionals.isJust @@ (Flows.flowStateValue @@ (Flows.unFlow @@ var "f" @@ var "state" @@ ref emptyTraceDef))

fromFlowDef :: Definition (a -> s -> Flow s a -> a)
fromFlowDef = tier1Definition "fromFlow" $
  doc "Get the value of a flow, or a default value if the flow fails" $
  functionN [aT, sT, flowSA, aT] $
  lambda "def" $ lambda "cx" $ lambda "f" $
      matchOpt (var "def") (lambda "x" $ var "x")
        @@ (Flows.flowStateValue @@ (Flows.unFlow @@ var "f" @@ var "cx" @@ ref emptyTraceDef))

mutateTraceDef :: Definition ((Trace -> Either_ String Trace) -> (Trace -> Trace -> Trace) -> Flow s a -> Flow s a)
mutateTraceDef = tier1Definition "mutateTrace" $
    functionN [
      Types.function traceT (eitherT stringT traceT),
      Types.functionN [traceT, traceT, traceT],
      flowSA,
      flowSA] $
    lambda "mutate" $ lambda "restore" $ lambda "f" $ wrap _Flow (
      lambda "s0" $ lambda "t0" (
        ((match _Either Nothing [
            _Either_left>>: var "forLeft",
            _Either_right>>: var "forRight"])
          @@ (var "mutate" @@ var "t0"))
        `with` [
          "forLeft">:
            lambda "msg" $ Flows.flowState nothing (var "s0") (ref pushErrorDef @@ var "msg" @@ var "t0"),
          -- retain the updated state, but reset the trace after execution
          "forRight">:
            lambda "t1" ((Flows.flowState
                (Flows.flowStateValue @@ var "f2")
                (Flows.flowStateState @@ var "f2")
                (var "restore" @@ var "t0" @@ (Flows.flowStateTrace @@ var "f2")))
              `with` [
                 -- execute the internal flow after augmenting the trace
                 "f2">: Flows.unFlow @@ var "f" @@ var "s0" @@ var "t1"
              ])]))
  where
    eitherT l r = Types.applyN [TypeVariable _Either, l, r]

pushErrorDef :: Definition (String -> Trace -> Trace)
pushErrorDef = tier1Definition "pushError" $
  doc "Push an error message" $
  lambda "msg" $ lambda "t" $ ((Flows.trace
      (Flows.traceStack @@ var "t")
      (Lists.cons @@ var "errorMsg" @@ (Flows.traceMessages @@ var "t"))
      (Flows.traceOther @@ var "t"))
    `with` [
      "errorMsg">: Strings.concat ["Error: ", var "msg", " (", (Strings.intercalate @@ " > " @@ (Lists.reverse @@ (Flows.traceStack @@ var "t"))), ")"]])

warnDef :: Definition (String -> Flow s a -> Flow s a)
warnDef = tier1Definition "warn" $
  doc "Continue the current flow after adding a warning message" $
  functionN [Types.string, flowSA, flowSA] $
  lambda "msg" $ lambda "b" $ wrap _Flow $ lambda "s0" $ lambda "t0" (
    (Flows.flowState
      (Flows.flowStateValue @@ var "f1")
      (Flows.flowStateState @@ var "f1")
      (var "addMessage" @@ (Flows.flowStateTrace @@ var "f1")))
    `with` [
      "f1">: Flows.unFlow @@ var "b" @@ var "s0" @@ var "t0",
      "addMessage">: lambda "t" $ Flows.trace
        (Flows.traceStack @@ var "t")
        (Lists.cons @@ ("Warning: " ++ var "msg") @@ (Flows.traceMessages @@ var "t"))
        (Flows.traceOther @@ var "t")])

withFlagDef :: Definition (String -> Flow s a -> Flow s a)
withFlagDef = tier1Definition "withFlag" $
  doc "Continue the current flow after setting a flag" $
  function Types.string (Types.function flowSA flowSA) $
  lambda "flag" ((ref mutateTraceDef @@ var "mutate" @@ var "restore")
  `with` [
    "mutate">: lambda "t" $ inject _Either _Either_right $ (Flows.trace
      (Flows.traceStack @@ var "t")
      (Flows.traceMessages @@ var "t")
      (Maps.insert @@ var "flag" @@ (inject _Term _Term_literal $ inject _Literal _Literal_boolean $ boolean True) @@ (Flows.traceOther @@ var "t"))),
    "restore">: lambda "ignored" $ lambda "t1" $ Flows.trace
      (Flows.traceStack @@ var "t1")
      (Flows.traceMessages @@ var "t1")
      (Maps.remove @@ var "flag" @@ (Flows.traceOther @@ var "t1"))])

withStateDef :: Definition (s1 -> Flow s1 a -> Flow s2 a)
withStateDef = tier1Definition "withState" $
  doc "Continue a flow using a given temporary state" $
  function (Types.var "s1") (Types.function flowS1A flowS2A) $
  lambda "cx0" $ lambda "f" $
    wrap _Flow $ lambda "cx1" $ lambda "t1" (
      (Flows.flowState (Flows.flowStateValue @@ var "f1") (var "cx1") (Flows.flowStateTrace @@ var "f1"))
      `with` [
        "f1">:
          typed (Types.apply (Types.apply (TypeVariable _FlowState) (Types.var "s1")) (Types.var "a")) $
          Flows.unFlow @@ var "f" @@ var "cx0" @@ var "t1"])

withTraceDef :: Definition (String -> Flow s a -> Flow s a)
withTraceDef = tier1Definition "withTrace" $
  doc "Continue the current flow after augmenting the trace" $
  functionN [Types.string, flowSA, flowSA] $
  lambda "msg" ((ref mutateTraceDef @@ var "mutate" @@ var "restore")
    `with` [
      -- augment the trace
      "mutate">: lambda "t" $ Logic.ifElse
        @@ (inject _Either _Either_left $ string "maximum trace depth exceeded. This may indicate an infinite loop")
        @@ (inject _Either _Either_right $ Flows.trace
          (Lists.cons @@ var "msg" @@ (Flows.traceStack @@ var "t"))
          (Flows.traceMessages @@ var "t")
          (Flows.traceOther @@ var "t"))
        @@ (Equality.gteInt32 @@ (Lists.length @@ (Flows.traceStack @@ var "t")) @@ ref maxTraceDepthDef),
      -- reset the trace stack after execution
      "restore">: lambda "t0" $ lambda "t1" $ Flows.trace
        (Flows.traceStack @@ var "t0")
        (Flows.traceMessages @@ var "t1")
        (Flows.traceOther @@ var "t1")])
