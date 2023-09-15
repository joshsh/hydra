module Hydra.StripSpec where

import Hydra.Kernel

import Hydra.TestUtils
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Char as C


checkStripTerm :: H.SpecWith ()
checkStripTerm = do
  H.describe "Tests for stripping annotations from terms" $ do
    H.it "Un-annotated terms are not affected" $
      QC.property $ \term -> case (term :: Term) of
        TermAnnotated _ -> True
        _ -> stripTerm term == term
    H.it "Terms are stripped recursively" $
      QC.property $ \term -> case (term :: Term) of
        TermAnnotated _ -> True
        _ -> stripTerm (Terms.annot emptyKv (Terms.annot emptyKv term)) == term

checkStripType :: H.SpecWith ()
checkStripType = do
  H.describe "Tests for stripping annotations from types" $ do
    H.it "Un-annotated types are not affected" $
      QC.property $ \typ -> case (typ :: Type Kv) of
        TypeAnnotated _ -> True
        _ -> stripType typ == typ
    H.it "Types are stripped recursively" $
      QC.property $ \typ -> case (typ :: Type Kv) of
        TypeAnnotated _ -> True
        _ -> stripType (Types.annot emptyKv (Types.annot emptyKv typ)) == typ

spec :: H.Spec
spec = do
  checkStripTerm
  checkStripType
