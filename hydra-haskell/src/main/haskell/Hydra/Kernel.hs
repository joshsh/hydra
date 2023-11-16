-- | A proxy for the Hydra kernel, i.e. the code which must be present in every Hydra implementation, and can be imported as a unit.

-- Note: Hydra.Grammar is part of the kernel, but is not a default import because the names of its types clash with those of other types.
module Hydra.Kernel (
  module Hydra.AdapterUtils,
  module Hydra.Adapters,
  module Hydra.Basics,
  module Hydra.Coders,
  module Hydra.Compute,
  module Hydra.Constants,
  module Hydra.Constraints,
  module Hydra.Core,
  module Hydra.CoreDecoding,
  module Hydra.CoreEncoding,
  module Hydra.CoreLanguage,
  module Hydra.Extras,
  module Hydra.Graph,
  module Hydra.Inference,
  module Hydra.Kv,
  module Hydra.Lexical,
  module Hydra.LiteralAdapters,
  module Hydra.Mantle,
  module Hydra.Module,
  module Hydra.Phantoms,
  module Hydra.Printing,
  module Hydra.Query,
  module Hydra.Reduction,
  module Hydra.Rewriting,
  module Hydra.Schemas,
  module Hydra.Strip,
  module Hydra.TermAdapters,
  module Hydra.Tier1,
  module Hydra.Tier2,
  module Hydra.Tier3,
  module Hydra.Tools.Debug,
  module Hydra.Tools.Formatting,
  module Hydra.Tools.Sorting,
  module Hydra.Workflow,
--  module Hydra.Ast,
--  module Hydra.Tools.GrammarToModule,
) where

import Hydra.AdapterUtils
import Hydra.Adapters
import Hydra.Basics
import Hydra.Coders
import Hydra.Compute
import Hydra.Constants
import Hydra.Constraints
import Hydra.Core
import Hydra.CoreDecoding
import Hydra.CoreEncoding
import Hydra.CoreLanguage
import Hydra.Extras
import Hydra.Graph
import Hydra.Inference
import Hydra.Kv
import Hydra.Lexical
import Hydra.LiteralAdapters
import Hydra.Mantle
import Hydra.Module
import Hydra.Phantoms
import Hydra.Printing
import Hydra.Query
import Hydra.Reduction
import Hydra.Rewriting
import Hydra.Schemas
import Hydra.Strip
import Hydra.TermAdapters
import Hydra.Tier1
import Hydra.Tier2
import Hydra.Tier3
import Hydra.Tools.Debug
import Hydra.Tools.Formatting
import Hydra.Tools.Sorting
import Hydra.Workflow
--import Hydra.Ast
--import Hydra.Tools.GrammarToModule
