module Hydra.ReductionSpec where

import Hydra.Kernel
import Hydra.Reduction
import Hydra.Dsl.Terms as Terms
import Hydra.Lib.Strings
import qualified Hydra.Dsl.Types as Types

import Hydra.TestUtils

import qualified Test.Hspec as H
import qualified Test.QuickCheck as QC
import qualified Data.List as L
import qualified Data.Char as C
import qualified Data.Set as S


checkAlphaConversion :: H.SpecWith ()
checkAlphaConversion = do
  H.describe "Tests for alpha conversion" $ do
    H.it "Variables are substituted at the top level" $
      QC.property $ \v ->
        alphaConvertTerm (Name v) (var $ v ++ "'") (var v) == (var (v ++ "'") :: Term)
    H.it "Variables are substituted within subexpressions" $
      QC.property $ \v ->
        alphaConvertTerm (Name v) (var $ v ++ "'") (list [int32 42, var v])
          == (list [int32 42, var (v ++ "'")] :: Term)
    H.it "Lambdas with unrelated variables are transparent to alpha conversion" $
      QC.property $ \v ->
        alphaConvertTerm (Name v) (var $ v ++ "1") (lambda (v ++ "2") $ list [int32 42, var v, var (v ++ "2")])
          == (lambda (v ++ "2") $ list [int32 42, var (v ++ "1"), var (v ++ "2")] :: Term)
    H.it "Lambdas of the same variable are opaque to alpha conversion" $
      QC.property $ \v ->
        alphaConvertTerm (Name v) (var $ v ++ "1") (lambda v $ list [int32 42, var v, var (v ++ "2")])
          == (lambda v $ list [int32 42, var v, var (v ++ "2")] :: Term)

checkLiterals :: H.SpecWith ()
checkLiterals = do
  H.describe "Tests for literal values" $ do

    H.it "Literal terms have no free variables" $
      QC.property $ \av -> termIsClosed (literal av :: Term)

    H.it "Literal terms are fully reduced; check using a dedicated function" $
      QC.property $ \av -> termIsValue testGraph (literal av :: Term)

    H.it "Literal terms are fully reduced; check by trying to reduce them" $
      QC.property $ \av ->
        shouldSucceedWith
          (eval (literal av))
          (literal av :: Term)

    H.it "Literal terms cannot be applied" $
      QC.property $ \lv -> shouldSucceedWith
        (eval $ apply (literal lv) (literal lv))
        (apply (literal lv) (literal lv))

checkMonomorphicPrimitives :: H.SpecWith ()
checkMonomorphicPrimitives = do
  H.describe "Tests for monomorphic primitive functions" $ do

    H.it "Example primitives have the expected arity" $ do
      H.shouldBe
        (primitiveArity <$> lookupPrimitive testGraph _strings_toUpper)
        (Just 1)
      H.shouldBe
        (primitiveArity <$> lookupPrimitive testGraph _strings_splitOn)
        (Just 2)

    H.it "Simple applications of a unary function succeed" $
      QC.property $ \s ->
        shouldSucceedWith
          (eval (apply (primitive _strings_toUpper) $ string s))
          (string $ fmap C.toUpper s)

    H.it "Simple applications of a binary function succeed" $
      QC.property $ \i1 i2 ->
        shouldSucceedWith
          (eval (apply (apply (primitive _math_add) $ int32 i1) $ int32 i2))
          (int32 $ i1 + i2)

    H.it "Incomplete application of a primitive function leaves the term unchanged" $
      QC.property $ \s1 ->
        shouldSucceedWith
          (eval (apply (primitive _strings_splitOn) $ string s1))
          (apply (primitive _strings_splitOn) $ string s1)

    H.it "Extra arguments to a primitive function are tolerated" $
      QC.property $ \s1 s2 ->
        shouldSucceedWith
          (eval (apply (apply (primitive _strings_toUpper) $ string s1) $ string s2))
          (apply (string $ toUpper s1) (string s2))

checkPolymorphicPrimitives :: H.SpecWith ()
checkPolymorphicPrimitives = do
  H.describe "Tests for polymorphic primitive functions" $ do

    H.it "Test polymorphic list length" $ do
      QC.property $ \l ->
        shouldSucceedWith
          (eval (apply (primitive _lists_length) $ list l))
          (int32 $ L.length l)

checkNullaryPrimitives :: H.SpecWith ()
checkNullaryPrimitives = do
  H.describe "Tests for nullary primitives (constants)" $ do

    H.it "Test empty set constant" $ do
      -- shouldSucceedWith
      --   (eval (apply (primitive _sets_size) (Terms.set S.empty)))
      --   (int32 0)
      shouldSucceedWith
        (eval (apply (primitive _sets_size) (primitive _sets_empty)))
        (int32 0)

testBetaReduceTypeRecursively :: H.SpecWith ()
testBetaReduceTypeRecursively = do
  H.describe "Beta reduce types recursively" $ do

    H.it "Try non-application types" $ do
      H.shouldBe
        (reduce Types.unit)
        Types.unit
      H.shouldBe
        (reduce testTypeLatLon)
        testTypeLatLon

    H.it "Try simple application types" $ do
      H.shouldBe
        (reduce app1)
        (Types.function Types.string Types.string)
      H.shouldBe
        (reduce app2)
        testTypeLatLon
      H.shouldBe
        (reduce app3)
        (TypeRecord $ RowType (Name "Example") Nothing [Types.field "foo" Types.unit])

    H.it "Try recursive application types" $ do
      H.shouldBe
        (reduce app4)
        (TypeRecord $ RowType (Name "Example") Nothing [Types.field "f1" Types.int32, Types.field "f2" Types.int64])

--    H.it "Distinguish between eager and lazy evaluation" $ do
--      H.shouldBe
--        (reduce False app5)
--        (TypeRecord $ RowType (Name "Example") Nothing [Types.field "foo" app1])
--      H.shouldBe
--        (reduce True app5)
--        (TypeRecord $ RowType (Name "Example") Nothing [Types.field "foo" $ Types.function Types.string Types.string])
  where
    app1 = Types.apply (Types.lambda "t" $ Types.function (Types.var "t") (Types.var "t")) Types.string :: Type
    app2 = Types.apply (Types.lambda "x" testTypeLatLon) Types.int32 :: Type
    app3 = Types.apply (Types.lambda "a" $ TypeRecord $ RowType (Name "Example") Nothing [Types.field "foo" $ Types.var "a"]) Types.unit :: Type
    app4 = Types.apply (Types.apply (Types.lambda "x" $ Types.lambda "y" $ TypeRecord $ RowType (Name "Example") Nothing [
      Types.field "f1" $ Types.var "x",
      Types.field "f2" $ Types.var "y"]) Types.int32) Types.int64 :: Type
    app5 = Types.apply (Types.lambda "a" $ TypeRecord $ RowType (Name "Example") Nothing [Types.field "foo" $ Types.var "a"]) app1

reduce :: Type -> Type
reduce typ = fromFlow typ (schemaContext testGraph) (betaReduceType typ)

spec :: H.Spec
spec = do
  checkAlphaConversion
  testBetaReduceTypeRecursively
  checkLiterals
  checkMonomorphicPrimitives
  checkPolymorphicPrimitives
  checkNullaryPrimitives
