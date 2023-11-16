module Hydra.Demos.AvroToPropertyGraphs where

import Hydra.Kernel
import Hydra.Tools.AvroWorkflows

import qualified System.FilePath as FP
import System.Directory


{-
import Hydra.Tools.AvroWorkflows
import Hydra.Demos.AvroToPropertyGraphs

transformAirplaneInfo propertyGraphLastMile
-}

transformAirplaneInfo :: LastMile Graph a -> IO ()
transformAirplaneInfo lastMile = do
  pwd <- getCurrentDirectory
  executeAvroTransformWorkflow lastMile $ TransformWorkflow "airplane info"
    (SchemaSpecFile $ FP.combine pwd "src/test/avro/AirplaneInfo.avsc")
    (FP.combine pwd "src/test/json")
    "/tmp/avro-pg-demo/output"
