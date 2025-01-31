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
import Hydra.Dsl.Mantle


tier1Definition :: String -> TTerm a -> TElement a
tier1Definition = definitionInModule hydraTier1Module

hydraTier1Module :: Module
hydraTier1Module = Module (Namespace "hydra/tier1") elements
    [hydraComputeModule, hydraConstantsModule, hydraStripModule] tier0Modules $
    Just ("A module for miscellaneous tier-1 functions and constants.")
  where
   elements = [
     el floatValueToBigfloatDef,
     el integerValueToBigintDef,
     el isLambdaDef,
     el unqualifyNameDef,
     -- Rewriting.hs
     el foldOverTermDef,
     el foldOverTypeDef,
     el freeVariablesInTermDef,
     el freeVariablesInTypeDef,
     el subtermsDef,
     el subtermsWithAccessorsDef,
     el subtypesDef,
     -- Flows.hs
     el emptyTraceDef,
     el flowSucceedsDef,
     el fromFlowDef,
     el mutateTraceDef,
     el pushErrorDef,
     el warnDef,
     el withFlagDef,
     el withStateDef,
     el withTraceDef
     ]

floatValueToBigfloatDef :: TElement (Double -> Double)
floatValueToBigfloatDef = tier1Definition "floatValueToBigfloat" $
  doc "Convert a floating-point value of any precision to a bigfloat" $
  function floatValueT Types.bigfloat $
  match _FloatValue Nothing [
    _FloatValue_bigfloat>>: Equality.identity,
    _FloatValue_float32>>: Literals.float32ToBigfloat,
    _FloatValue_float64>>: Literals.float64ToBigfloat]

integerValueToBigintDef :: TElement (IntegerValue -> Integer)
integerValueToBigintDef = tier1Definition "integerValueToBigint" $
  doc "Convert an integer value of any precision to a bigint" $
  function integerValueT Types.bigint $
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

isLambdaDef :: TElement (Term -> Bool)
isLambdaDef = tier1Definition "isLambda" $
  doc "Check whether a term is a lambda, possibly nested within let and/or annotation terms" $
  function termT Types.boolean $
  lambda "term" $ (match _Term (Just false) [
      _Term_function>>: match _Function (Just false) [
        _Function_lambda>>: constant true],
      _Term_let>>: lambda "lt" (ref isLambdaDef @@ (project _Let _Let_environment @@ var "lt"))])
    @@ (ref fullyStripTermDef @@ var "term")

-- Rewriting.hs

foldOverTermDef :: TElement (TraversalOrder -> (x -> Term -> x) -> x -> Term -> x)
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

foldOverTypeDef :: TElement (TraversalOrder -> (x -> Type -> x) -> x -> Type -> x)
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

freeVariablesInTermDef :: TElement (Term -> S.Set Name)
freeVariablesInTermDef = tier1Definition "freeVariablesInTerm" $
  doc "Find the free variables (i.e. variables not bound by a lambda or let) in a term" $
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

freeVariablesInTypeDef :: TElement (Type -> S.Set Name)
freeVariablesInTypeDef = tier1Definition "freeVariablesInType" $
  doc "Find the free variables (i.e. variables not bound by a lambda or let) in a type" $
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

subtermsDef :: TElement (Term -> [Term])
subtermsDef = tier1Definition "subterms" $
  doc "Find the children of a given term" $
  function termT (listT termT) $
  match _Term Nothing [
    _Term_annotated>>: lambda "at" $ list [Core.annotatedTermSubject @@ var "at"],
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
      @@ (Lists.map @@ Core.letBindingTerm @@ (Core.letBindings @@ var "lt")),
    _Term_list>>: lambda "l" $ var "l",
    _Term_literal>>: constant $ list [],
    _Term_map>>: lambda "m" (Lists.concat @@
      (Lists.map @@ (lambda "p" $ list [first @@ var "p", second @@ var "p"]) @@ (Maps.toList @@ var "m"))),
    _Term_optional>>: matchOpt (list []) (lambda "t" $ list [var "t"]),
    _Term_product>>: lambda "tuple" $ var "tuple",
    _Term_record>>: lambda "rt" (Lists.map @@ Core.fieldTerm @@ (Core.recordFields @@ var "rt")),
    _Term_set>>: Sets.toList,
    _Term_sum>>: lambda "st" $ list [Core.sumTerm @@ var "st"],
    _Term_typeAbstraction>>: lambda "ta" $ list [Core.typeAbstractionBody @@ var "ta"],
    _Term_typeApplication>>: lambda "ta" $ list [Core.typedTermTerm @@ var "ta"],
    _Term_typed>>: lambda "tt" $ list [Core.typedTermTerm @@ var "tt"],
    _Term_union>>: lambda "ut" $ list [Core.fieldTerm @@ (Core.injectionField @@ var "ut")],
    _Term_variable>>: constant $ list [],
    _Term_wrap>>: lambda "n" $ list [Core.wrappedTermObject @@ var "n"]]

subtermsWithAccessorsDef :: TElement (Term -> [(TermAccessor, Term)])
subtermsWithAccessorsDef = tier1Definition "subtermsWithAccessors" $
  doc "Find the children of a given term" $
  function termT (listT $ pairT termAccessorT termT) $
  match _Term Nothing [
    _Term_annotated>>: lambda "at" $ single termAccessorAnnotatedSubject $ Core.annotatedTermSubject @@ var "at",
    _Term_application>>: lambda "p" $ list [
      result termAccessorApplicationFunction $ Core.applicationFunction @@ var "p",
      result termAccessorApplicationArgument $ Core.applicationArgument @@ var "p"],
    _Term_function>>: match _Function (Just none) [
        _Function_elimination>>: match _Elimination (Just none) [
            _Elimination_list>>: lambda "fld" $ single termAccessorListFold $ var "fld",
            _Elimination_optional>>: lambda "oc" $ list [
              result termAccessorOptionalCasesNothing $ Core.optionalCasesNothing @@ var "oc",
              result termAccessorOptionalCasesJust $ Core.optionalCasesJust @@ var "oc"],
            _Elimination_union>>: lambda "cs" $ Lists.concat2
              @@ ((matchOpt none (lambda "t" $ single termAccessorUnionCasesDefault $ var "t")) @@ (Core.caseStatementDefault @@ var "cs"))
              @@ (Lists.map
                @@ (lambda "f" $ result (termAccessorUnionCasesBranch $ Core.fieldName @@ var "f") $ Core.fieldTerm @@ var "f")
                @@ (Core.caseStatementCases @@ var "cs"))],
        _Function_lambda>>: lambda "l" $ single termAccessorLambdaBody $ Core.lambdaBody @@ var "l"],
    _Term_let>>: lambda "lt" $ Lists.cons
      @@ (result termAccessorLetEnvironment $ Core.letEnvironment @@ var "lt")
      @@ (Lists.map
        @@ (lambda "b" $ result (termAccessorLetBinding $ Core.letBindingName @@ var "b") $ Core.letBindingTerm @@ var "b")
        @@ (Core.letBindings @@ var "lt")),
    _Term_list>>: Lists.map
      -- TODO: use a range of indexes from 0 to len(l)-1, rather than just 0
      @@ (lambda "e" $ result (termAccessorListElement $ int32 0) $ var "e"),
    _Term_literal>>: constant none,
    _Term_map>>: lambda "m" (Lists.concat @@
      (Lists.map
        @@ (lambda "p" $ list [
          -- TODO: use a range of indexes from 0 to len(l)-1, rather than just 0
          result (termAccessorMapKey $ int32 0) $ first @@ var "p",
          result (termAccessorMapValue $ int32 0) $ second @@ var "p"])
        @@ (Maps.toList @@ var "m"))),
    _Term_optional>>: matchOpt none (lambda "t" $ single termAccessorOptionalTerm $ var "t"),
    _Term_product>>: Lists.map
      -- TODO: use a range of indexes from 0 to len(l)-1, rather than just 0
      @@ (lambda "e" $ result (termAccessorProductTerm $ int32 0) $ var "e"),
    _Term_record>>: lambda "rt" (Lists.map
      @@ (lambda "f" $ result (termAccessorRecordField $ Core.fieldName @@ var "f") $ Core.fieldTerm @@ var "f")
      @@ (Core.recordFields @@ var "rt")),
    _Term_set>>: lambda "s" $ Lists.map
      -- TODO: use a range of indexes from 0 to len(l)-1, rather than just 0
      @@ (lambda "e" $ result (termAccessorListElement $ int32 0) $ var "e")
      @@ (Sets.toList @@ var "s"),
    _Term_sum>>: lambda "st" $
      single termAccessorSumTerm $
      Core.sumTerm @@ var "st",
    _Term_typeAbstraction>>: lambda "ta" $
      single termAccessorTypeAbstractionBody $
      Core.typeAbstractionBody @@ var "ta",
    _Term_typeApplication>>: lambda "ta" $
      single termAccessorTypeApplicationTerm $
      Core.typedTermTerm @@ var "ta",
    _Term_typed>>: lambda "tt" $
      single termAccessorTypedTerm $
      Core.typedTermTerm @@ var "tt",
    _Term_union>>: lambda "ut" $
      single termAccessorInjectionTerm $
      Core.fieldTerm @@ (Core.injectionField @@ var "ut"),
    _Term_variable>>: constant none,
    _Term_wrap>>: lambda "n" $ single termAccessorWrappedTerm $ Core.wrappedTermObject @@ var "n"]
  where
    none = list []
    single accessor term = list [result accessor term]
    result accessor term = pair accessor term
    simple term = result termAccessorAnnotatedSubject term

subtypesDef :: TElement (Type -> [Type])
subtypesDef = tier1Definition "subtypes" $
  doc "Find the children of a given type expression" $
  function typeT (listT typeT) $
  match _Type Nothing [
    _Type_annotated>>: lambda "at" $ list [Core.annotatedTypeSubject @@ var "at"],
    _Type_application>>: lambda "at" $ list [
      Core.applicationTypeFunction @@ var "at",
      Core.applicationTypeArgument @@ var "at"],
    _Type_function>>: lambda "ft" $ list [
      Core.functionTypeDomain @@ var "ft",
      Core.functionTypeCodomain @@ var "ft"],
    _Type_lambda>>: lambda "lt" $ list [Core.lambdaTypeBody @@ var "lt"],
    _Type_list>>: lambda "lt" $ list [var "lt"],
    _Type_literal>>: constant $ list [],
    _Type_map>>: lambda "mt" $ list [
      Core.mapTypeKeys @@ var "mt",
      Core.mapTypeValues @@ var "mt"],
    _Type_optional>>: lambda "ot" $ list [var "ot"],
    _Type_product>>: lambda "pt" $ var "pt",
    _Type_record>>: lambda "rt" (Lists.map @@ Core.fieldTypeType @@ (Core.rowTypeFields @@ var "rt")),
    _Type_set>>: lambda "st" $ list [var "st"],
    _Type_sum>>: lambda "st" $ var "st",
    _Type_union>>: lambda "rt" (Lists.map @@ Core.fieldTypeType @@ (Core.rowTypeFields @@ var "rt")),
    _Type_variable>>: constant $ list [],
    _Type_wrap>>: lambda "nt" $ list [Core.wrappedTypeObject @@ var "nt"]]

unqualifyNameDef :: TElement (QualifiedName -> Name)
unqualifyNameDef = tier1Definition "unqualifyName" $
  doc "Convert a qualified name to a dot-separated name" $
  function qualifiedNameT nameT $
  lambda "qname" $ (wrap _Name $ var "prefix" ++ (project _QualifiedName _QualifiedName_local @@ var "qname"))
    `with` [
      "prefix">: matchOpt (string "") (lambda "n" $ (unwrap _Namespace @@ var "n") ++ string ".")
        @@ (project _QualifiedName _QualifiedName_namespace @@ var "qname")]

-- Flows.hs

emptyTraceDef :: TElement Trace
emptyTraceDef = tier1Definition "emptyTrace" $
  record _Trace [
    _Trace_stack>>: list [],
    _Trace_messages>>: list [],
    _Trace_other>>: Maps.empty]

flowSucceedsDef :: TElement (Flow s a -> Bool)
flowSucceedsDef = tier1Definition "flowSucceeds" $
  doc "Check whether a flow succeeds" $
  function (Types.var "s") (Types.function flowSAT Types.boolean) $
  lambda "cx" $ lambda "f" $
    Optionals.isJust @@ (Flows.flowStateValue @@ (Flows.unFlow @@ var "f" @@ var "cx" @@ ref emptyTraceDef))

fromFlowDef :: TElement (a -> s -> Flow s a -> a)
fromFlowDef = tier1Definition "fromFlow" $
  doc "Get the value of a flow, or a default value if the flow fails" $
  function (Types.var "a") (Types.function (Types.var "s") (Types.function flowSAT (Types.var "a"))) $
  lambda "def" $ lambda "cx" $ lambda "f" $
      matchOpt (var "def") (lambda "x" $ var "x")
        @@ (Flows.flowStateValue @@ (Flows.unFlow @@ var "f" @@ var "cx" @@ ref emptyTraceDef))

mutateTraceDef :: TElement ((Trace -> Either_ String Trace) -> (Trace -> Trace -> Trace) -> Flow s a -> Flow s a)
mutateTraceDef = tier1Definition "mutateTrace" $
    functionN [
      Types.function traceT (eitherT Types.string traceT),
      Types.functionN [traceT, traceT, traceT],
      flowSAT,
      flowSAT] $
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
            function traceT (flowStateT (Types.var "s") (Types.var "s")) $
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

pushErrorDef :: TElement (String -> Trace -> Trace)
pushErrorDef = tier1Definition "pushError" $
  doc "Push an error message" $
  functionN [Types.string, traceT, traceT] $
  lambda "msg" $ lambda "t" $ ((Flows.trace
      (Flows.traceStack @@ var "t")
      (Lists.cons @@ var "errorMsg" @@ (Flows.traceMessages @@ var "t"))
      (Flows.traceOther @@ var "t"))
    `with` [
      "errorMsg">: Strings.concat ["Error: ", var "msg", " (", (Strings.intercalate @@ " > " @@ (Lists.reverse @@ (Flows.traceStack @@ var "t"))), ")"]])

warnDef :: TElement (String -> Flow s a -> Flow s a)
warnDef = tier1Definition "warn" $
  doc "Continue the current flow after adding a warning message" $
  functionN [Types.string, flowSAT, flowSAT] $
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

withFlagDef :: TElement (String -> Flow s a -> Flow s a)
withFlagDef = tier1Definition "withFlag" $
  doc "Continue the current flow after setting a flag" $
  function nameT (Types.function flowSAT flowSAT) $
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

withStateDef :: TElement (s1 -> Flow s1 a -> Flow s2 a)
withStateDef = tier1Definition "withState" $
  doc "Continue a flow using a given state" $
  function (Types.var "s1") (Types.function flowS1AT flowS2AT) $
  lambda "cx0" $ lambda "f" $
    wrap _Flow $ lambda "cx1" $ lambda "t1" (
      (Flows.flowState (Flows.flowStateValue @@ var "f1") (var "cx1") (Flows.flowStateTrace @@ var "f1"))
      `with` [
        "f1">:
          typed (Types.apply (Types.apply (TypeVariable _FlowState) (Types.var "s1")) (Types.var "a")) $
          Flows.unFlow @@ var "f" @@ var "cx0" @@ var "t1"])

withTraceDef :: TElement (String -> Flow s a -> Flow s a)
withTraceDef = tier1Definition "withTrace" $
  doc "Continue the current flow after augmenting the trace" $
  functionN [Types.string, flowSAT, flowSAT] $
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
