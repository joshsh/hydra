module Hydra.Sources.Tier3.All(
  module Hydra.Sources.Tier3.All,
  module Hydra.Sources.Tier2.All,
  module Hydra.Sources.Tier3.Tier3,
) where

import Hydra.Sources.Tier2.All
import Hydra.Sources.Tier3.Tier3

kernelModules :: [Module]
kernelModules = tier0Modules ++ tier1Modules ++ tier2Modules ++ tier3Modules

tier3Modules :: [Module]
tier3Modules = [
  hydraTier3Module]
