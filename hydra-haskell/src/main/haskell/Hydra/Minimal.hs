-- | A minimal, standalone Hydra kernel which allows external tools (like @wisnesky's Algorithm W implementation)
--   to take a lightweight dependency on Hydra types or functions, without requiring compilation of Hydra proper.
--   There are two versions of this module:
--   * External: has all of the necessary Hydra definitions in one file
--   * Internal: just exports the appropriate symbols from the actual Hydra modules

module Hydra.Minimal (
  FloatType(..),
  FloatValue(..),
  IntegerType(..),
  IntegerValue(..),
  Literal(..),
  LiteralType(..),
  Name(..),
  floatValueType,
  integerValueType,
  int32,
  literalType,
  string,
) where

import Hydra.Core
import Hydra.Basics
import Hydra.Dsl.Literals
