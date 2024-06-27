-- | Haskell implementations of hydra/lib/flows primitives

module Hydra.Lib.Flows where

import Hydra.Compute
import qualified Hydra.Tier1 as Tier1

import qualified Control.Monad as CM


-- Haskell-specific helpers

instance Functor (Flow s) where
  fmap = CM.liftM
instance Applicative (Flow s) where
  pure x = Flow $ \s t -> FlowState (Just x) s t
  (<*>) = CM.ap
instance Monad (Flow s) where
  return = Prelude.pure
  p >>= k = Flow q'
    where
      q' s0 t0 = FlowState y s2 t2
        where
          FlowState x s1 t1 = unFlow p s0 t0
          FlowState y s2 t2 = case x of
            Just x' -> unFlow (k x') s1 t1
            Nothing -> FlowState Nothing s1 t1
instance MonadFail (Flow s) where
  fail msg = Flow $ \s t -> FlowState Nothing s (Tier1.pushError msg t)

-- Primitive functions

apply :: Flow s (x -> y) -> Flow s x -> Flow s y
apply = (<*>)

bind :: Flow s x -> (x -> Flow s y) -> Flow s y
bind = (>>=)

fail :: String -> Flow s x
fail = CM.fail

map :: (x -> y) -> Flow s x -> Flow s y
map = fmap

pure :: x -> Flow s x
pure = return

sequence :: [Flow s x] -> Flow s [x]
sequence = CM.sequence
