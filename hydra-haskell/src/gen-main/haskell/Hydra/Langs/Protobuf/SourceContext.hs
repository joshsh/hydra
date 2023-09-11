-- | Based on https://github.com/protocolbuffers/protobuf/blob/main/src/google/protobuf/source_context.proto

module Hydra.Langs.Protobuf.SourceContext where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | `SourceContext` represents information about the source of a protobuf element, like the file in which it is defined.
data SourceContext = 
  SourceContext {
    -- | The path-qualified name of the .proto file that contained the associated protobuf element.  For example: `"google/protobuf/source_context.proto"`.
    sourceContextFileName :: String}
  deriving (Eq, Ord, Read, Show)

_SourceContext = (Core.Name "hydra/langs/protobuf/sourceContext.SourceContext")

_SourceContext_fileName = (Core.FieldName "fileName")