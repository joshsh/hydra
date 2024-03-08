module Hydra.Langs.Yaml.Modules (moduleToYaml) where

import Hydra.Kernel
import Hydra.Adapters
import Hydra.Langs.Yaml.Serde
import Hydra.Langs.Yaml.Language
import qualified Hydra.Langs.Yaml.Model as YM
import qualified Hydra.Dsl.Types as Types

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M


constructModule ::
  Module
  -> M.Map Type (Coder Graph Graph Term YM.Node)
  -> [Element]
  -> Flow Graph YM.Node
constructModule mod coders els = do
    keyvals <- withTrace "encoding terms" (CM.mapM toYaml els)
    return $ YM.NodeMapping $ M.fromList keyvals
  where
    toYaml el = withTrace ("element " ++ unName (elementName el)) $ do
      let term = elementData el
      typ <- requireTermType term
      encode <- case M.lookup typ coders of
        Nothing -> fail $ "no coder found for type " ++ show typ
        Just coder -> pure $ coderEncode coder
      node <- encode term
      return (YM.NodeScalar $ YM.ScalarStr $ localNameOf $ elementName el, node)
    ns = unNamespace $ moduleNamespace mod
    localNameOf name = L.drop (1 + L.length ns) $ unName name

moduleToYaml :: Module -> Flow Graph (M.Map FilePath String)
moduleToYaml mod = withTrace ("print module " ++ (unNamespace $ moduleNamespace mod)) $ do
    node <- transformModule yamlLanguage encodeTerm constructModule mod
    return $ M.fromList [(path, hydraYamlToString node)]
  where
    path = namespaceToFilePath False (FileExtension "yaml") $ moduleNamespace mod
    encodeTerm _ = fail $ "only type definitions are expected in this mapping to YAML"
