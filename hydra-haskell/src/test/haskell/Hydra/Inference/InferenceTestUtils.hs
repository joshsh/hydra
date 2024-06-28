module Hydra.Inference.InferenceTestUtils where

import Hydra.Kernel
import qualified Hydra.Dsl.Types as Types
import Hydra.TestUtils

import qualified Test.Hspec as H


checkType :: Term -> Type -> H.Expectation
checkType term typ = expectTypeAnnotation pure term typ

executeFlow = fromFlow (TermLiteral $ LiteralString "no term") testGraph

expectFailure :: Term -> H.Expectation
expectFailure term = do
  shouldFail (inferredTypeOf term)

expectType :: Term -> Type -> H.Expectation
expectType term typ = do
  shouldSucceedWith
    (inferredTypeOf term)
    typ

expectPolytype :: Term -> [String] -> Type -> H.Expectation
expectPolytype term vars typ = do
  shouldSucceedWith
    (inferredTypeOf term)
    (Types.lambdas vars typ)

expectRawType :: Term -> Type -> H.Expectation
expectRawType term typ = do
  shouldSucceedWith
    (inferredType <$> infer term)
    typ

expectTypeAnnotation :: (Term -> Flow Graph Term) -> Term -> Type -> H.Expectation
expectTypeAnnotation path term etyp = shouldSucceedWith atyp etyp
  where
   atyp = do
     iterm <- inferTermType term
     selected <- path iterm
     requireTermType selected
