-- | A module for miscellaneous tier-1 functions and constants.

module Hydra.Tier1 where

import qualified Hydra.Coders as Coders
import qualified Hydra.Compute as Compute
import qualified Hydra.Constants as Constants
import qualified Hydra.Core as Core
import qualified Hydra.Lib.Equality as Equality
import qualified Hydra.Lib.Lists as Lists
import qualified Hydra.Lib.Literals as Literals
import qualified Hydra.Lib.Logic as Logic
import qualified Hydra.Lib.Maps as Maps
import qualified Hydra.Lib.Optionals as Optionals
import qualified Hydra.Lib.Sets as Sets
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Mantle as Mantle
import qualified Hydra.Module as Module
import qualified Hydra.Strip as Strip
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | Convert a floating-point value of any precision to a bigfloat
floatValueToBigfloat :: (Core.FloatValue -> Double)
floatValueToBigfloat x = case x of
  Core.FloatValueBigfloat v -> (Equality.identity v)
  Core.FloatValueFloat32 v -> (Literals.float32ToBigfloat v)
  Core.FloatValueFloat64 v -> (Literals.float64ToBigfloat v)

-- | Convert an integer value of any precision to a bigint
integerValueToBigint :: (Core.IntegerValue -> Integer)
integerValueToBigint x = case x of
  Core.IntegerValueBigint v -> (Equality.identity v)
  Core.IntegerValueInt8 v -> (Literals.int8ToBigint v)
  Core.IntegerValueInt16 v -> (Literals.int16ToBigint v)
  Core.IntegerValueInt32 v -> (Literals.int32ToBigint v)
  Core.IntegerValueInt64 v -> (Literals.int64ToBigint v)
  Core.IntegerValueUint8 v -> (Literals.uint8ToBigint v)
  Core.IntegerValueUint16 v -> (Literals.uint16ToBigint v)
  Core.IntegerValueUint32 v -> (Literals.uint32ToBigint v)
  Core.IntegerValueUint64 v -> (Literals.uint64ToBigint v)

-- | Check whether a term is a lambda, possibly nested within let and/or annotation terms
isLambda :: (Core.Term a -> Bool)
isLambda term = ((\x -> case x of
  Core.TermFunction v -> ((\x -> case x of
    Core.FunctionLambda _ -> True
    _ -> False) v)
  Core.TermLet v -> (isLambda (Core.letEnvironment v))
  _ -> False) (Strip.stripTerm term))

-- | Convert a qualified name to a dot-separated name
unqualifyName :: (Module.QualifiedName -> Core.Name)
unqualifyName qname =  
  let prefix = ((\x -> case x of
          Nothing -> ""
          Just v -> (Strings.cat [
            Module.unNamespace v,
            "."])) (Module.qualifiedNameNamespace qname))
  in (Core.Name (Strings.cat [
    prefix,
    (Module.qualifiedNameLocal qname)]))

-- | Fold over a term, traversing its subterms in the specified order
foldOverTerm :: (Ord a) => (Coders.TraversalOrder -> (x -> Core.Term a -> x) -> x -> Core.Term a -> x)
foldOverTerm order fld b0 term = ((\x -> case x of
  Coders.TraversalOrderPre -> (L.foldl (foldOverTerm order fld) (fld b0 term) (subterms term))
  Coders.TraversalOrderPost -> (fld (L.foldl (foldOverTerm order fld) b0 (subterms term)) term)) order)

-- | Fold over a type, traversing its subtypes in the specified order
foldOverType :: (Coders.TraversalOrder -> (x -> Core.Type a -> x) -> x -> Core.Type a -> x)
foldOverType order fld b0 typ = ((\x -> case x of
  Coders.TraversalOrderPre -> (L.foldl (foldOverType order fld) (fld b0 typ) (subtypes typ))
  Coders.TraversalOrderPost -> (fld (L.foldl (foldOverType order fld) b0 (subtypes typ)) typ)) order)

-- | Find the free variables (i.e. variables not bound by a lambda or let) in a term
freeVariablesInTerm :: (Ord a) => (Core.Term a -> Set Core.Name)
freeVariablesInTerm term =  
  let dfltVars = (L.foldl (\s -> \t -> Sets.union s (freeVariablesInTerm t)) Sets.empty (subterms term))
  in ((\x -> case x of
    Core.TermFunction v -> ((\x -> case x of
      Core.FunctionLambda v -> (Sets.remove (Core.lambdaParameter v) (freeVariablesInTerm (Core.lambdaBody v)))
      _ -> dfltVars) v)
    Core.TermVariable v -> (Sets.singleton v)
    _ -> dfltVars) term)

-- | Find the free variables (i.e. variables not bound by a lambda or let) in a type
freeVariablesInType :: (Core.Type a -> Set Core.Name)
freeVariablesInType typ =  
  let dfltVars = (L.foldl (\s -> \t -> Sets.union s (freeVariablesInType t)) Sets.empty (subtypes typ))
  in ((\x -> case x of
    Core.TypeLambda v -> (Sets.remove (Core.lambdaTypeParameter v) (freeVariablesInType (Core.lambdaTypeBody v)))
    Core.TypeVariable v -> (Sets.singleton v)
    _ -> dfltVars) typ)

-- | Find the children of a given term
subterms :: (Ord a) => (Core.Term a -> [Core.Term a])
subterms x = case x of
  Core.TermAnnotated v -> [
    Core.annotatedSubject v]
  Core.TermApplication v -> [
    Core.applicationFunction v,
    (Core.applicationArgument v)]
  Core.TermFunction v -> ((\x -> case x of
    Core.FunctionElimination v -> ((\x -> case x of
      Core.EliminationList v -> [
        v]
      Core.EliminationOptional v -> [
        Core.optionalCasesNothing v,
        (Core.optionalCasesJust v)]
      Core.EliminationUnion v -> (Lists.concat2 ((\x -> case x of
        Nothing -> []
        Just v -> [
          v]) (Core.caseStatementDefault v)) (Lists.map Core.fieldTerm (Core.caseStatementCases v)))
      _ -> []) v)
    Core.FunctionLambda v -> [
      Core.lambdaBody v]
    _ -> []) v)
  Core.TermLet v -> (Lists.cons (Core.letEnvironment v) (Lists.map snd (Maps.toList (Core.letBindings v))))
  Core.TermList v -> v
  Core.TermLiteral _ -> []
  Core.TermMap v -> (Lists.concat (Lists.map (\p -> [
    fst p,
    (snd p)]) (Maps.toList v)))
  Core.TermOptional v -> ((\x -> case x of
    Nothing -> []
    Just v -> [
      v]) v)
  Core.TermProduct v -> v
  Core.TermRecord v -> (Lists.map Core.fieldTerm (Core.recordFields v))
  Core.TermSet v -> (Sets.toList v)
  Core.TermStream _ -> []
  Core.TermSum v -> [
    Core.sumTerm v]
  Core.TermUnion v -> [
    Core.fieldTerm (Core.injectionField v)]
  Core.TermVariable _ -> []
  Core.TermWrap v -> [
    Core.nominalObject v]

-- | Find the children of a given type expression
subtypes :: (Core.Type a -> [Core.Type a])
subtypes x = case x of
  Core.TypeAnnotated v -> [
    Core.annotatedSubject v]
  Core.TypeApplication v -> [
    Core.applicationTypeFunction v,
    (Core.applicationTypeArgument v)]
  Core.TypeFunction v -> [
    Core.functionTypeDomain v,
    (Core.functionTypeCodomain v)]
  Core.TypeLambda v -> [
    Core.lambdaTypeBody v]
  Core.TypeList v -> [
    v]
  Core.TypeLiteral _ -> []
  Core.TypeMap v -> [
    Core.mapTypeKeys v,
    (Core.mapTypeValues v)]
  Core.TypeOptional v -> [
    v]
  Core.TypeProduct v -> v
  Core.TypeRecord v -> (Lists.map Core.fieldTypeType (Core.rowTypeFields v))
  Core.TypeSet v -> [
    v]
  Core.TypeSum v -> v
  Core.TypeUnion v -> (Lists.map Core.fieldTypeType (Core.rowTypeFields v))
  Core.TypeVariable _ -> []
  Core.TypeWrap v -> [
    Core.nominalObject v]

emptyTrace :: (Compute.Trace)
emptyTrace = Compute.Trace {
  Compute.traceStack = [],
  Compute.traceMessages = [],
  Compute.traceOther = Maps.empty}

-- | Check whether a flow succeeds
flowSucceeds :: (s -> Compute.Flow s a -> Bool)
flowSucceeds cx f = (Optionals.isJust (Compute.flowStateValue (Compute.unFlow f cx emptyTrace)))

-- | Get the value of a flow, or a default value if the flow fails
fromFlow :: (a -> s -> Compute.Flow s a -> a)
fromFlow def cx f = ((\x -> case x of
  Nothing -> def
  Just v -> v) (Compute.flowStateValue (Compute.unFlow f cx emptyTrace)))

mutateTrace :: ((Compute.Trace -> Mantle.Either_ String Compute.Trace) -> (Compute.Trace -> Compute.Trace -> Compute.Trace) -> Compute.Flow s a -> Compute.Flow s a)
mutateTrace mutate restore f = (Compute.Flow (\s0 -> \t0 ->  
  let forLeft = (\msg -> Compute.FlowState {
          Compute.flowStateValue = Nothing,
          Compute.flowStateState = s0,
          Compute.flowStateTrace = (pushError msg t0)}) 
      forRight = (\t1 ->  
              let f2 = (Compute.unFlow f s0 t1)
              in Compute.FlowState {
                Compute.flowStateValue = (Compute.flowStateValue f2),
                Compute.flowStateState = (Compute.flowStateState f2),
                Compute.flowStateTrace = (restore t0 (Compute.flowStateTrace f2))})
  in ((\x -> case x of
    Mantle.EitherLeft v -> (forLeft v)
    Mantle.EitherRight v -> (forRight v)) (mutate t0))))

-- | Push an error message
pushError :: (String -> Compute.Trace -> Compute.Trace)
pushError msg t =  
  let errorMsg = (Strings.cat [
          "Error: ",
          msg,
          " (",
          Strings.intercalate " > " (Lists.reverse (Compute.traceStack t)),
          ")"])
  in Compute.Trace {
    Compute.traceStack = (Compute.traceStack t),
    Compute.traceMessages = (Lists.cons errorMsg (Compute.traceMessages t)),
    Compute.traceOther = (Compute.traceOther t)}

-- | Continue the current flow after adding a warning message
warn :: (String -> Compute.Flow s a -> Compute.Flow s a)
warn msg b = (Compute.Flow (\s0 -> \t0 ->  
  let addMessage = (\t -> Compute.Trace {
          Compute.traceStack = (Compute.traceStack t),
          Compute.traceMessages = (Lists.cons (Strings.cat [
            "Warning: ",
            msg]) (Compute.traceMessages t)),
          Compute.traceOther = (Compute.traceOther t)}) 
      f1 = (Compute.unFlow b s0 t0)
  in Compute.FlowState {
    Compute.flowStateValue = (Compute.flowStateValue f1),
    Compute.flowStateState = (Compute.flowStateState f1),
    Compute.flowStateTrace = (addMessage (Compute.flowStateTrace f1))}))

-- | Continue the current flow after setting a flag
withFlag :: (String -> Compute.Flow s a -> Compute.Flow s a)
withFlag flag =  
  let mutate = (\t -> Mantle.EitherRight (Compute.Trace {
          Compute.traceStack = (Compute.traceStack t),
          Compute.traceMessages = (Compute.traceMessages t),
          Compute.traceOther = (Maps.insert flag (Core.TermLiteral (Core.LiteralBoolean True)) (Compute.traceOther t))})) 
      restore = (\ignored -> \t1 -> Compute.Trace {
              Compute.traceStack = (Compute.traceStack t1),
              Compute.traceMessages = (Compute.traceMessages t1),
              Compute.traceOther = (Maps.remove flag (Compute.traceOther t1))})
  in (mutateTrace mutate restore)

-- | Continue a flow using a given state
withState :: (s1 -> Compute.Flow s1 a -> Compute.Flow s2 a)
withState cx0 f = (Compute.Flow (\cx1 -> \t1 ->  
  let f1 = (Compute.unFlow f cx0 t1)
  in Compute.FlowState {
    Compute.flowStateValue = (Compute.flowStateValue f1),
    Compute.flowStateState = cx1,
    Compute.flowStateTrace = (Compute.flowStateTrace f1)}))

-- | Continue the current flow after augmenting the trace
withTrace :: (String -> Compute.Flow s a -> Compute.Flow s a)
withTrace msg =  
  let mutate = (\t -> Logic.ifElse (Mantle.EitherLeft "maximum trace depth exceeded. This may indicate an infinite loop") (Mantle.EitherRight (Compute.Trace {
          Compute.traceStack = (Lists.cons msg (Compute.traceStack t)),
          Compute.traceMessages = (Compute.traceMessages t),
          Compute.traceOther = (Compute.traceOther t)})) (Equality.gteInt32 (Lists.length (Compute.traceStack t)) Constants.maxTraceDepth)) 
      restore = (\t0 -> \t1 -> Compute.Trace {
              Compute.traceStack = (Compute.traceStack t0),
              Compute.traceMessages = (Compute.traceMessages t1),
              Compute.traceOther = (Compute.traceOther t1)})
  in (mutateTrace mutate restore)