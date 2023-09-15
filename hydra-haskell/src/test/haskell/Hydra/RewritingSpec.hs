{-# LANGUAGE OverloadedStrings #-}

module Hydra.RewritingSpec where

import Hydra.Kernel
import Hydra.Dsl.Terms
import Hydra.Flows

import Hydra.TestUtils

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Set as S


data Quux a = QuuxUnit | QuuxValue a | QuuxPair (Quux a) (Quux a) deriving (Eq, Ord, Show)

fsubQuux :: (a -> b) -> (Quux a -> Quux b) -> Quux a -> Quux b
fsubQuux mf recurse q = case q of
  QuuxUnit -> QuuxUnit
  QuuxValue x -> QuuxValue $ mf x
  QuuxPair left right -> QuuxPair (recurse left) (recurse right)

rewriteQuux :: (a -> b) -> ((Quux a -> Quux b) -> Quux a -> Quux b) -> Quux a -> Quux b
rewriteQuux mf f = rewrite (fsubQuux mf) f

myQuuxRewriter :: Quux String -> Quux Int
myQuuxRewriter = rewriteQuux L.length $ \fsub q -> fsub $ case q of
  QuuxPair left right -> QuuxPair QuuxUnit right
  _ -> q

testExpandLambdas :: H.SpecWith ()
testExpandLambdas = do
  H.describe "Test expanding to lambda terms" $ do

    H.it "Try some terms which do not expand" $ do
      noChange (int32 42)
      noChange (list ["foo", "bar"])
      noChange
        (apply (apply splitOn "foo") "bar")
      noChange
        (lambda "x" $ int32 42)

    H.it "Expand bare function terms" $ do
      expandsTo
        toLower
        (lambda "v1" $ apply toLower (var "v1"))
      expandsTo
        splitOn
        (lambda "v1" $ lambda "v2" $ apply (apply splitOn (var "v1")) (var "v2"))
      expandsTo
        (matchOpt (int32 42) length)
        -- Note two levels of lambda expansion
        (lambda "v1" $ apply (matchOpt (int32 42) (lambda "v1" $ apply length $ var "v1")) (var "v1"))

    H.it "Expand subterms within applications" $ do
      expandsTo
        (apply splitOn "bar")
        (lambda "v1" $ apply (apply splitOn "bar") (var "v1"))
      expandsTo
        (apply (lambda "x" $ var "x") length)
        (apply (lambda "x" $ var "x") (lambda "v1" $ apply length $ var "v1"))

    H.it "Expand arbitrary subterms" $ do
      expandsTo
        (list [lambda "x" "foo", apply splitOn "bar"])
        (list [lambda "x" "foo", lambda "v1" $ apply (apply splitOn "bar") $ var "v1"])

    H.it "Check that lambda expansion is idempotent" $ do
      QC.property $ \term -> do
        once <- fromFlowIo testGraph $ expandLambdas term
        twice <- fromFlowIo testGraph $ expandLambdas once
        H.shouldBe once twice
  where
    length = primitive $ Name "hydra/lib/strings.length"
    splitOn = primitive $ Name "hydra/lib/strings.splitOn"
    toLower = primitive $ Name "hydra/lib/strings.toLower"
    expandsTo termBefore termAfter = do
      result <- fromFlowIo testGraph $ expandLambdas termBefore
      H.shouldBe result termAfter

    noChange term = expandsTo term term

testFoldOverTerm :: H.SpecWith ()
testFoldOverTerm = do
  H.describe "Test folding over terms" $ do

    H.it "Try a simple fold" $ do
      H.shouldBe
        (foldOverTerm TraversalOrderPre addInt32s 0
          (list [int32 42, apply (lambda "x" $ var "x") (int32 10)] :: Term Kv))
        52

    H.it "Check that traversal order is respected" $ do
      H.shouldBe
        (foldOverTerm TraversalOrderPre listLengths []
          (list [list [string "foo", string "bar"], apply (lambda "x" $ var "x") (list [string "quux"])] :: Term Kv))
        [1, 2, 2]
      H.shouldBe
        (foldOverTerm TraversalOrderPost listLengths []
          (list [list [string "foo", string "bar"], apply (lambda "x" $ var "x") (list [string "quux"])] :: Term Kv))
        [2, 1, 2]
  where
    addInt32s sum term = case term of
      TermLiteral (LiteralInteger (IntegerValueInt32 i)) -> sum + i
      _ -> sum
    listLengths l term = case term of
      TermList els -> L.length els:l
      _ -> l

testFreeVariablesInTerm :: H.SpecWith ()
testFreeVariablesInTerm = do
  H.describe "Test free variables" $ do

--    H.it "Generated terms never have free variables" $ do
--      QC.property $ \(TypedTerm _ term) -> do
--        H.shouldBe
--          (freeVariablesInTerm (term :: Term Kv))
--          S.empty

    H.it "Free variables in individual terms" $ do
      H.shouldBe
        (freeVariablesInTerm (string "foo" :: Term Kv))
        S.empty
      H.shouldBe
        (freeVariablesInTerm (var "x" :: Term Kv))
        (S.fromList [Name "x"])
      H.shouldBe
        (freeVariablesInTerm (list [var "x", apply (lambda "y" $ var "y") (int32 42)] :: Term Kv))
        (S.fromList [Name "x"])
      H.shouldBe
        (freeVariablesInTerm (list [var "x", apply (lambda "y" $ var "y") (var "y")] :: Term Kv))
        (S.fromList [Name "x", Name "y"])

--testReplaceFreeName :: H.SpecWith ()
--testReplaceFreeName = do
--  H.describe "Test replace free type variables" $ do
--
--    H.it "Check that variable types are replaced" $ do
--      H.shouldBe
--        (replaceFreeName (Name "v1") Types.string $ Types.var "v")
--        ()

testReplaceTerm :: H.SpecWith ()
testReplaceTerm = do
    H.describe "Test term replacement" $ do

      H.it "Check that the correct subterms are replaced" $ do
        H.shouldBe
          (rewriteTerm replaceInts keepKv
            (int32 42))
          (int64 42 :: Term Kv)
        H.shouldBe
          (rewriteTerm replaceInts keepKv
            (list [int32 42, apply (lambda "x" $ var "x") (int32 137)]))
          (list [int64 42, apply (lambda "x" $ var "x") (int64 137)] :: Term Kv)

      H.it "Check that traversal order is respected" $ do
        H.shouldBe
          (rewriteTerm replaceListsPre keepKv
            (list [list [list []]]))
          (list [list []] :: Term Kv)
        H.shouldBe
          (rewriteTerm replaceListsPost keepKv
            (list [list [list []]]))
          (list [] :: Term Kv)

--      H.it "Check that metadata is replace recursively" $ do
--        H.shouldBe
--          (rewriteTerm keepTerm replaceKv (list [annot 42 (string "foo")] :: Term Int))
--          (list [annot "42" (string "foo")])
  where
    keepTerm recurse term = recurse term

    keepKv = id

    replaceInts recurse term = case term2 of
        TermLiteral (LiteralInteger (IntegerValueInt32 v)) -> int64 $ fromIntegral v
        _ -> term2
      where
        term2 = recurse term

    replaceLists term = case term of
      TermList (h:_) -> case h of
        TermList [] -> list []
        _ -> term
      _ -> term

    replaceListsPre recurse = recurse . replaceLists

    replaceListsPost recurse = replaceLists . recurse

    replaceKv i = show i

testRewriteExampleType :: H.SpecWith ()
testRewriteExampleType = do
    H.describe "Test rewriting of a made-up recursive type" $ do

      H.it "Rewrite a hand-picked expression" $ do
        H.shouldBe
          quux2
          (myQuuxRewriter quux1)
  where
    quux1 = QuuxPair QuuxUnit (QuuxPair (QuuxValue "abc") (QuuxValue "12345"))
    quux2 = QuuxPair QuuxUnit (QuuxPair QuuxUnit (QuuxValue 5))

testSimplifyTerm :: H.SpecWith ()
testSimplifyTerm = do
  H.describe "Test term simplifation (optimization)" $ do

    H.it "Check that 'const' applications are simplified" $ do
      H.shouldBe
        (simplifyTerm (apply (lambda "x" (string "foo")) (int32 42)))
        (string "foo" :: Term Kv)
      H.shouldBe
        (simplifyTerm (apply (lambda "x" $ list [var "x", var "x"]) (var "y")))
        (list [var "y", var "y"] :: Term Kv)
      H.shouldBe
        (simplifyTerm (apply (lambda "x" $ string "foo") (var "y")))
        (string "foo" :: Term Kv)
      H.shouldBe
        (simplifyTerm (apply (lambda "x"
          (apply (lambda "a" (list [string "foo", var "a"])) (var "x"))) (var "y")))
        (list [string "foo", var "y"] :: Term Kv)

--testStripKv :: H.SpecWith ()
--testStripKv = do
--  H.describe "Test stripping metadata from terms" $ do
--
--    H.it "Strip type annotations" $ do
--      QC.property $ \(TypedTerm typ term) -> do
--        shouldSucceedWith
--          (typeOf term)
--          Nothing
--        shouldSucceedWith
--          (typeOf $ withType testGraph typ term)
--          (Just typ)
--        shouldSucceedWith
--          (typeOf $ strip $ withType testGraph typ term)
--          Nothing

typeOf term = annotationClassTermType (graphAnnotations testGraph) term

withType :: Graph Kv -> Type Kv -> Term Kv -> Term Kv
withType g typ = annotationClassSetTermType (graphAnnotations g) (Just typ)

spec :: H.Spec
spec = do
  testExpandLambdas
  testFoldOverTerm
  testFreeVariablesInTerm
--  testReplaceFreeName
  testReplaceTerm
  testRewriteExampleType
  testSimplifyTerm
--  testStripKv -- TODO: restore me
