module Hydra.Langs.Yaml.Serde where

import Hydra.Kernel
import Hydra.Langs.Yaml.Coder
import Hydra.Tools.Bytestrings
import qualified Hydra.Langs.Yaml.Model as YM

import qualified Data.ByteString.Lazy as BS
import qualified Control.Monad as CM
import qualified Data.YAML as DY
import qualified Data.YAML.Event as DYE
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.ByteString.Lazy.Char8 as LB


bytesToHsYaml :: BS.ByteString -> Flow (Graph) (DY.Node DY.Pos)
bytesToHsYaml bs = case DY.decodeNode bs of
    Left (pos, msg) -> fail $ "YAML parser failure at " ++ show pos ++ ": " ++ msg
    Right docs -> if L.null docs
      then fail "no YAML document"
      else if L.length docs > 1
      then fail "multiple YAML documents"
      else case L.head docs of
        (DY.Doc node) -> pure node

bytesToHydraYaml :: BS.ByteString -> Flow (Graph) YM.Node
bytesToHydraYaml = bytesToHsYaml CM.>=> hsYamlToHydraYaml

hsYamlToBytes :: DY.Node () -> BS.ByteString
hsYamlToBytes node = DY.encodeNode [DY.Doc node]

hsYamlToHydraYaml :: DY.Node x -> Flow (Graph) YM.Node
hsYamlToHydraYaml hs = case hs of
  DY.Scalar _ s -> YM.NodeScalar <$> case s of
     DY.SNull -> pure YM.ScalarNull
     DY.SBool b -> pure $ YM.ScalarBool b
     DY.SFloat f -> pure $ YM.ScalarFloat f
     DY.SInt i -> pure $ YM.ScalarInt i
     DY.SStr t -> pure $ YM.ScalarStr $ T.unpack t
     DY.SUnknown _ _ -> fail "YAML unknown scalars are unsupported"
  DY.Mapping _ _ m -> YM.NodeMapping . M.fromList <$> CM.mapM mapPair (M.toList m)
    where
      mapPair (k, v) = (,) <$> hsYamlToHydraYaml k <*> hsYamlToHydraYaml v
  DY.Sequence _ _ s -> YM.NodeSequence <$> CM.mapM hsYamlToHydraYaml s
  DY.Anchor {} -> fail "YAML anchors are unsupported"

hydraYamlToBytes :: YM.Node -> BS.ByteString
hydraYamlToBytes = hsYamlToBytes . hydraYamlToHsYaml

hydraYamlToHsYaml :: YM.Node -> DY.Node ()
hydraYamlToHsYaml hy = case hy of
  YM.NodeMapping m -> DY.Mapping () DYE.untagged $ M.fromList $ mapPair <$> M.toList m
    where
      mapPair (k, v) = (,) (hydraYamlToHsYaml k) (hydraYamlToHsYaml v)
  YM.NodeScalar s -> DY.Scalar () $ case s of
    YM.ScalarBool b -> DY.SBool b
    YM.ScalarFloat f -> DY.SFloat f
    YM.ScalarInt i -> DY.SInt i
    YM.ScalarNull -> DY.SNull
    YM.ScalarStr s -> DY.SStr $ T.pack s
  YM.NodeSequence s -> DY.Sequence () DYE.untagged $ hydraYamlToHsYaml <$> s

hydraYamlToString :: YM.Node -> String
hydraYamlToString = bytesToString . hydraYamlToBytes

yamlByteStringCoder :: Type -> Flow (Graph) (Coder (Graph) (Graph) Term BS.ByteString)
yamlByteStringCoder typ = do
  coder <- yamlCoder typ
  return Coder {
    coderEncode = fmap hydraYamlToBytes . coderEncode coder,
    coderDecode = bytesToHydraYaml CM.>=> coderDecode coder}

yamlStringCoder :: Type -> Flow (Graph) (Coder (Graph) (Graph) Term String)
yamlStringCoder typ = do
  serde <- yamlByteStringCoder typ
  return Coder {
    coderEncode = fmap LB.unpack . coderEncode serde,
    coderDecode = coderDecode serde . LB.pack}
