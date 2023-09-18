-- | Abstractions for single- and bidirectional transformations

module Hydra.Compute where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | A two-level bidirectional encoder which adapts types to types and terms to terms
data Adapter s1 s2 t1 t2 v1 v2 = 
  Adapter {
    adapterIsLossy :: Bool,
    adapterSource :: t1,
    adapterTarget :: t2,
    adapterCoder :: (Coder s1 s2 v1 v2)}

_Adapter = (Core.Name "hydra/compute.Adapter")

_Adapter_isLossy = (Core.FieldName "isLossy")

_Adapter_source = (Core.FieldName "source")

_Adapter_target = (Core.FieldName "target")

_Adapter_coder = (Core.FieldName "coder")

-- | A two-level encoder and decoder, operating both at a type level and an instance (data) level
data Bicoder s1 s2 t1 t2 v1 v2 = 
  Bicoder {
    bicoderEncode :: (t1 -> Adapter s1 s2 t1 t2 v1 v2),
    bicoderDecode :: (t2 -> Adapter s2 s1 t2 t1 v2 v1)}

_Bicoder = (Core.Name "hydra/compute.Bicoder")

_Bicoder_encode = (Core.FieldName "encode")

_Bicoder_decode = (Core.FieldName "decode")

-- | An encoder and decoder; a bidirectional flow between two types
data Coder s1 s2 v1 v2 = 
  Coder {
    coderEncode :: (v1 -> Flow s1 v2),
    coderDecode :: (v2 -> Flow s2 v1)}

_Coder = (Core.Name "hydra/compute.Coder")

_Coder_encode = (Core.FieldName "encode")

_Coder_decode = (Core.FieldName "decode")

-- | A variant of the State monad with built-in logging and error handling
newtype Flow s a = 
  Flow {
    unFlow :: (s -> Trace -> FlowState s a)}

_Flow = (Core.Name "hydra/compute.Flow")

-- | The result of evaluating a Flow
data FlowState s a = 
  FlowState {
    flowStateValue :: (Maybe a),
    flowStateState :: s,
    flowStateTrace :: Trace}
  deriving (Eq, Ord, Read, Show)

_FlowState = (Core.Name "hydra/compute.FlowState")

_FlowState_value = (Core.FieldName "value")

_FlowState_state = (Core.FieldName "state")

_FlowState_trace = (Core.FieldName "trace")

-- | A container for logging and error information
data Trace = 
  Trace {
    traceStack :: [String],
    traceMessages :: [String],
    -- | A map of string keys to arbitrary terms as values, for application-specific use
    traceOther :: (Map String Core.Term)}
  deriving (Eq, Ord, Read, Show)

_Trace = (Core.Name "hydra/compute.Trace")

_Trace_stack = (Core.FieldName "stack")

_Trace_messages = (Core.FieldName "messages")

_Trace_other = (Core.FieldName "other")