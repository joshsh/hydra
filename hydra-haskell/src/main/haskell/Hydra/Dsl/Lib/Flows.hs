module Hydra.Dsl.Lib.Flows where

import Hydra.Dsl.Base
import Hydra.Core
import Hydra.Compute
import Hydra.Phantoms
import Hydra.Sources.Libraries
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Data.Map as M


-- Primitives

apply :: Datum (Flow s (a -> b) -> Flow s a -> Flow s b)
apply = Datum $ Terms.primitive _flows_apply

bind :: Datum (Flow s a -> (a -> Flow s b) -> Flow s b)
bind = Datum $ Terms.primitive _flows_bind

fail :: Datum (String -> Flow s a)
fail = Datum $ Terms.primitive _flows_fail

map :: Datum ((a -> b) -> Flow s a -> Flow s b)
map = Datum $ Terms.primitive _flows_map

pure :: Datum (a -> Flow s a)
pure = Datum $ Terms.primitive _flows_pure

-- Accessors

flowState :: Datum (Maybe a) -> Datum s -> Datum Trace -> Datum (FlowState s a)
flowState value state trace = record _FlowState [
    _FlowState_value>>: value,
    _FlowState_state>>: state,
    _FlowState_trace>>: trace]

flowStateState :: Datum (FlowState s a -> s)
flowStateState = project _FlowState _FlowState_state

flowStateTrace :: Datum (FlowState s a -> Trace)
flowStateTrace = project _FlowState _FlowState_trace

flowStateValue :: Datum (FlowState s a -> Maybe a)
flowStateValue = project _FlowState _FlowState_value

trace :: Datum [String] -> Datum [String] -> Datum (M.Map String Term) -> Datum Trace
trace stack messages other = record _Trace [
    _Trace_stack>>: stack,
    _Trace_messages>>: messages,
    _Trace_other>>: other]
    
traceStack :: Datum (Trace -> [String])
traceStack = project _Trace _Trace_stack

traceMessages :: Datum (Trace -> [String])
traceMessages = project _Trace _Trace_messages

traceOther :: Datum (Trace -> M.Map String Term)
traceOther = project _Trace _Trace_other

unFlow :: Datum (Flow s a -> s -> Trace -> FlowState s a)
unFlow = unwrap _Flow
