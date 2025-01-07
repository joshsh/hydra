module Hydra.Ext.Python.Serde where

import qualified Hydra.Ext.Python.Syntax as Py
import Hydra.Tools.Serialization

import qualified Hydra.Ast as A


encodeFile :: Py.File -> A.Expr
encodeFile f = cst "foo"
