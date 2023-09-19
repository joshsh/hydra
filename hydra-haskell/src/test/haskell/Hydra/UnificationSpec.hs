module Hydra.UnificationSpec where

import Hydra.Kernel
import Hydra.Unification
import Hydra.TestUtils
import qualified Hydra.Dsl.Types as Types

import qualified Test.Hspec as H
import qualified Data.Map as M


expectUnify :: [Constraint] -> [(Name, Type)] -> H.Expectation
expectUnify constraints subst = shouldSucceedWith
  (solveConstraints constraints)
  (M.fromList subst)

expectUnify2 :: Type -> Type -> [(Name, Type)] -> H.Expectation
expectUnify2 t1 t2 = expectUnify [(t1, t2)]

checkIndividualConstraints :: H.SpecWith ()
checkIndividualConstraints = H.describe "Check a few hand-crafted constraints" $ do

    H.it "Unify nothing" $
      expectUnify [] []

    H.it "Unify variable with variable" $
      expectUnify2
        (Types.var "a")
        (Types.var "b")
        [(Name "b", Types.var "a")]

    H.it "Unify variable with literal type" $
      expectUnify2
        (Types.var "a")
        (Types.string)
        [(Name "a", Types.string)]

checkUniversalTypes :: H.SpecWith ()
checkUniversalTypes = H.describe "Check universal types" $ do

  H.it "Unify polymorphic list (with free variable) with monomorphic list" $
    expectUnify2
      (Types.list (Types.var "a"))
      (Types.list Types.string)
      [(Name "a", Types.string)]

  H.it "Unify two polymorphic lists (with free variables)" $
    expectUnify2
      (Types.list $ Types.var "a")
      (Types.list $ Types.var "b")
      [(Name "b", Types.var "a")]

  H.it "Unify polymorphic list (with universal type) with monomorphic list" $
    expectUnify2
      (Types.lambda "a" $ Types.list (Types.var "a"))
      (Types.list Types.string)
      [(Name "a", Types.string)]

  H.it "Unify two polymorphic lists (with universal types)" $
    expectUnify2
      (Types.lambda "a" $ Types.list $ Types.var "a")
      (Types.lambda "b" $ Types.list $ Types.var "b")
      [(Name "b", Types.var "a")]

spec :: H.Spec
spec = do
  checkIndividualConstraints
  checkUniversalTypes
