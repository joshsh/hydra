module Hydra.AnnotationsSpec where

import Hydra.Kernel
import qualified Hydra.Dsl.Terms as Terms
import Hydra.TestUtils

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.Map as M


checkArbitraryAnnotations :: H.SpecWith ()
checkArbitraryAnnotations = H.describe "Check getting/setting of arbitrary annotations" $ do

    H.it "Set a single key/value pair" $
      QC.property $ \k v -> H.shouldBe
        (setAnn k (Just $ Terms.int32 v) $ Terms.string "foo")
        (TermAnnotated $ Annotated (Terms.string "foo") $ Kv $ M.fromList [(k, Terms.int32 v)])

    H.it "Retrieve a single value" $
      QC.property $ \k v -> H.shouldBe
        (getAnn k $ setAnn k (Just $ Terms.string v) $ Terms.int32 42)
        (Just $ Terms.string v)

    H.it "Retrieve a null value" $
      QC.property $ \k -> H.shouldBe
        (getAnn k $ Terms.int16 42)
        Nothing

    H.it "Set multiple values" $
      QC.property $ \v1 v2 -> H.shouldBe
        (setAnn "k2" (Just $ Terms.int32 v2) $
          setAnn "k1" (Just $ Terms.string v1) $
          Terms.boolean True)
        (TermAnnotated $ Annotated (Terms.boolean True) $ Kv $ M.fromList [("k1", Terms.string v1), ("k2", Terms.int32 v2)])

    H.it "An outer annotation overrides an inner one" $
      QC.property $ \k v1 v2 -> H.shouldBe
        (setAnn k (Just $ Terms.string v2) $ setAnn k (Just $ Terms.string v1) $ Terms.string "bar")
        (TermAnnotated $ Annotated (Terms.string "bar") $ Kv $ M.fromList [(k, Terms.string v2)])

    H.it "Unset a single annotation" $
      QC.property $ \k -> H.shouldBe
        (setAnn k Nothing $ setAnn k (Just $ Terms.string "foo") $ Terms.int64 137)
        (Terms.int64 137)

    H.it "Unset one of multiple annotations" $
      QC.property $ \v1 v2 -> H.shouldBe
        (setAnn "k1" Nothing $
          setAnn "k2" (Just $ Terms.int32 v2) $
          setAnn "k1" (Just $ Terms.string v1) $
          Terms.int64 137)
        (TermAnnotated $ Annotated (Terms.int64 137) $ Kv $ M.fromList [("k2", Terms.int32 v2)])

checkDescriptions :: H.SpecWith ()
checkDescriptions = H.describe "Check getting/setting of descriptions" $ do

    H.it "Set a single description" $
      QC.property $ \d -> H.shouldBe
        (setDesc (Just d) $ Terms.string "foo")
        (TermAnnotated $ Annotated (Terms.string "foo") $ Kv $ M.fromList [("description", Terms.string d)])

    H.it "Retrieve a single description" $
      QC.property $ \d -> H.shouldBe
        (getDesc $ setDesc (Just d) $ Terms.int32 42)
        (Just d)

    H.it "Retrieve a null description" $
      QC.property $ \i -> H.shouldBe
        (getDesc $ Terms.int16 i)
        Nothing

    H.it "An outer description overrides an inner one" $
      QC.property $ \d1 d2 -> H.shouldBe
        (setDesc (Just d2) $ setDesc (Just d1) $ Terms.string "bar")
        (TermAnnotated $ Annotated (Terms.string "bar") $ Kv $ M.fromList [("description", Terms.string d2)])

    H.it "Unset a description" $
      QC.property $ \d -> H.shouldBe
        (setDesc Nothing $ setDesc (Just d) $ Terms.int64 137)
        (Terms.int64 137)

checkNoncompactAnnotations :: H.SpecWith ()
checkNoncompactAnnotations = H.describe "Check non-compact (i.e. layered) annotations" $ do

    H.it "Annotations at different levels, with different keys, are all available" $ do
      H.shouldBe
        (getTermAnnotation "one" term0)
        Nothing
      H.shouldBe
        (getTermAnnotation "one" term1)
        (Just $ Terms.int32 1)
      H.shouldBe
        (getTermAnnotation "one" term2)
        (Just $ Terms.int32 1)
      H.shouldBe
        (getTermAnnotation "two" term2)
        (Just $ Terms.int32 2)
      H.shouldBe
        (getTermAnnotation "two" term3)
        (Just $ Terms.int32 2)

    H.it "Outer annotations override inner ones" $
      H.shouldBe
        (getTermAnnotation "one" term3)
        (Just $ Terms.int32 42)

  where
    term0 = Terms.int32 42
    term1 = Terms.annot (Kv $ M.fromList [("one", Terms.int32 1)]) term0
    term2 = Terms.annot (Kv $ M.fromList [("two", Terms.int32 2)]) term1
    term3 = Terms.annot (Kv $ M.fromList [("one", Terms.int32 42)]) term2

getAnn = getTermAnnotation

getDesc term = fromFlow (Just "no description") testGraph $ getTermDescription term

setAnn = setTermAnnotation

setDesc = setTermDescription

spec :: H.Spec
spec = do
  checkArbitraryAnnotations
  checkDescriptions
  checkNoncompactAnnotations
