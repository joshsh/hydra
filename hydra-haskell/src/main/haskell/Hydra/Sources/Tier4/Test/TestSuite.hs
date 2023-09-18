module Hydra.Sources.Tier4.Test.TestSuite (testSuiteModule) where

import Hydra.Testing
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types
import Hydra.Sources.Tier3.All

import Hydra.Sources.Tier4.Test.Lib.Lists
import Hydra.Sources.Tier4.Test.Lib.Strings


testSuiteNs = Namespace "hydra/test/testSuite"

testSuiteModule :: Module
testSuiteModule = Module testSuiteNs elements [hydraCoreModule, hydraTestingModule] $
    Just "Test cases for primitive functions"
  where
    elements = [
      groupElement "allTests" allTests]

groupElement :: String -> TestGroup -> Element
groupElement lname group = Element name $ setTermType (Just typ) $ encodeGroup group
  where
    encodeGroup (TestGroup name desc groups cases) = Terms.record _TestGroup [
      Field _TestGroup_name $ Terms.string name,
      Field _TestGroup_description $ Terms.optional (Terms.string <$> desc),
      Field _TestGroup_subgroups $ Terms.list (encodeGroup <$> groups),
      Field _TestGroup_cases $ Terms.list (encodeCase <$> cases)]
    encodeCase (TestCase desc style input output) = Terms.record _TestCase [
      Field _TestCase_description $ Terms.optional (Terms.string <$> desc),
      Field _TestCase_evaluationStyle $ Terms.variant _EvaluationStyle (case style of
        EvaluationStyleEager -> _EvaluationStyle_eager
        EvaluationStyleLazy -> _EvaluationStyle_lazy) Terms.unit,
      Field _TestCase_input $ coreEncodeTerm input,
      Field _TestCase_output $ coreEncodeTerm output]
    name = unqualifyName $ QualifiedName (Just testSuiteNs) lname
    typ = TypeVariable _TestGroup

allTests :: TestGroup
allTests = TestGroup "All tests" Nothing primTests []
  where
    primTests = [
      listPrimitiveTests,
      stringPrimitiveTests]
