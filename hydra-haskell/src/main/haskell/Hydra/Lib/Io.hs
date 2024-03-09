-- | Tier-1 library which provides Haskell implementations of hydra/lib/io primitives.

module Hydra.Lib.Io (
  showTerm,
  showType,
) where

import Hydra.Core
import Hydra.Compute
import Hydra.Graph
import Hydra.Langs.Json.Coder
import Hydra.Dsl.Annotations
import Hydra.Langs.Json.Serde
import Hydra.CoreEncoding
--import Hydra.Rewriting
import Hydra.Annotations
import Hydra.Tier1
import qualified Hydra.Json as Json
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Data.Map as M
import qualified Data.Maybe as Y


noGraph :: Graph
noGraph = Graph {
  graphElements = M.empty,
  graphEnvironment = M.empty,
  graphTypes = M.empty,
  graphBody = Terms.list [],
  graphPrimitives = M.empty,
  graphSchema = Nothing}


-- | Use the "debugging" JSON encoding for now
showTerm :: Term -> String
showTerm term = tryFlow $ do
    json <- jsonEncodeTerm $ coreEncodeTerm term
    return $ jsonValueToString json
  where
    tryFlow f = case flowStateValue result of
        Nothing -> "JSON write error: " ++ show (traceMessages $ flowStateTrace result)
        Just s -> s
      where
        result = unFlow f () emptyTrace

--showTerm :: Term -> String
--showTerm term = fromFlow "fail" noGraph $ do
--    coder <- termStringCoder
--    coderEncode coder encoded
--  where
--    encoded = coreEncodeTerm $ rewriteTermAnnotations (const $ M.empty) term

termStringCoder :: Flow Graph (Coder Graph Graph Term String)
termStringCoder = do
    termJsonCoder <- jsonCoder $ TypeVariable _Term
    return $ Coder (mout termJsonCoder) (min termJsonCoder)
  where
    mout termJsonCoder term = jsonValueToString <$> coderEncode termJsonCoder term
    min termJsonCoder s = case stringToJsonValue s of
      Left msg -> fail $ "failed to parse JSON value: " ++ msg
      Right v -> coderDecode termJsonCoder v

showType :: Type -> String
showType typ = fromFlow "fail" noGraph $ do
    coder <- typeStringCoder
    coderEncode coder encoded
  where
--    encoded = coreEncodeType $ rewriteTypeAnnotations (const $ M.empty) typ
    encoded = coreEncodeType typ

typeStringCoder :: Flow Graph (Coder Graph Graph Term String)
typeStringCoder = do
    typeJsonCoder <- jsonCoder $ TypeVariable _Type
    return $ Coder (mout typeJsonCoder) (min typeJsonCoder)
  where
    mout typeJsonCoder term = jsonValueToString <$> coderEncode typeJsonCoder term
    min typeJsonCoder s = case stringToJsonValue s of
      Left msg -> fail $ "failed to parse as JSON value: " ++ msg
      Right v -> coderDecode typeJsonCoder v
