-- | A simple JSON model. This model is part of the Hydra kernel, despite JSON being an external language; JSON support is built in to Hydra

module Hydra.Sources.Tier0.Json where

-- Standard Tier-0 imports
import qualified Data.List             as L
import qualified Data.Map              as M
import qualified Data.Set              as S
import qualified Data.Maybe            as Y
import           Hydra.Dsl.Annotations
import           Hydra.Dsl.Bootstrap
import qualified Hydra.Dsl.Terms       as Terms
import           Hydra.Dsl.Types       as Types
import           Hydra.Kernel
import           Hydra.Sources.Core


jsonModelModule :: Module
jsonModelModule = Module ns elements [] $
    Just "A JSON syntax model. See the BNF at https://www.json.org"
  where
    ns = Namespace "hydra/json"
    def = datatype ns
    json = typeref ns

    elements = [

      def "Value" $
        doc "A JSON value" $
        union [
          "array">: list $ json "Value",
          "boolean">: boolean,
          "null">: unit,
          "number">: bigfloat, -- TODO: JSON numbers are decimal-encoded
          "object">: Types.map string (json "Value"),
          "string">: string]]
