-- | Non-kernel functions for working with Hydra's built-in Flow monad in Haskell

module Hydra.Flows where

import Hydra.Kernel

import qualified Control.Monad as CM
import qualified System.IO as IO


fromFlowIo :: s -> Flow s a -> IO.IO a
fromFlowIo cx f = case mv of
    Just v -> return v
    Nothing -> CM.fail $ traceSummary trace
  where
    FlowState mv _ trace = unFlow f cx emptyTrace
