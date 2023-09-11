module Hydra.Langs.Json.Eliminate where

import Hydra.Kernel
import qualified Hydra.Json as Json

import qualified Data.Map as M


expectArray :: Json.Value -> Flow s [Json.Value]
expectArray value = case value of
  Json.ValueArray els -> pure els
  _ -> unexpected "JSON array" $ show value

expectNumber :: Json.Value -> Flow s Double
expectNumber value = case value of
  Json.ValueNumber d -> pure d
  _ -> unexpected "JSON number" $ show value

expectObject :: Json.Value -> Flow s (M.Map String Json.Value)
expectObject value = case value of
  Json.ValueObject m -> pure m
  _ -> unexpected "JSON object" $ show value

expectString :: Json.Value -> Flow s String
expectString value = case value of
  Json.ValueString s -> pure s
  _ -> unexpected "JSON string" $ show value

opt :: String -> M.Map String Json.Value -> Maybe Json.Value
opt = M.lookup

optArray :: String -> M.Map String Json.Value -> Flow s (Maybe [Json.Value])
optArray fname m = case opt fname m of
  Nothing -> pure Nothing
  Just a -> Just <$> expectArray a

optString :: String -> M.Map String Json.Value -> Flow s (Maybe String)
optString fname m = case opt fname m of
  Nothing -> pure Nothing
  Just s -> Just <$> expectString s

require :: String -> M.Map String Json.Value -> Flow s Json.Value
require fname m = case M.lookup fname m of
  Nothing -> fail $ "required attribute " ++ show fname ++ " not found"
  Just value -> pure value

requireArray :: String -> M.Map String Json.Value -> Flow s [Json.Value]
requireArray fname m = require fname m >>= expectArray

requireNumber :: String -> M.Map String Json.Value -> Flow s Double
requireNumber fname m = require fname m >>= expectNumber

requireString :: String -> M.Map String Json.Value -> Flow s String
requireString fname m = require fname m >>= expectString
