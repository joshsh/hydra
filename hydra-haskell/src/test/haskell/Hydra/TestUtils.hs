module Hydra.TestUtils (
  checkLiteralAdapter,
  checkFieldAdapter,
  checkFloatAdapter,
  checkIntegerAdapter,
  checkDataAdapter,
  checkSerdeRoundTrip,
  checkSerialization,
  eval,
  shouldFail,
  shouldFailIn,
  shouldSucceed,
  shouldSucceedIn,
  shouldSucceedWith,
  shouldSucceedInWith,
  strip,
  termTestContext,
  module Hydra.TestGraph,
) where

import Hydra.Kernel
import Hydra.LiteralAdapters
import Hydra.TermAdapters
import Hydra.AdapterUtils

import Hydra.TestGraph
import Hydra.ArbitraryCore()

import qualified Test.Hspec as H
import qualified Test.HUnit.Lang as HL
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y
import qualified Data.ByteString.Lazy as BS


baseLanguage :: Language
baseLanguage = hydraCoreLanguage

baseContext :: AdapterContext
baseContext = AdapterContext testGraph baseLanguage M.empty

checkAdapter :: (Eq t, Eq v, Show t, Show v)
  => (v -> v)
  -> (t -> Flow AdapterContext (SymmetricAdapter AdapterContext t v))
  -> ([r] -> AdapterContext)
  -> [r] -> t -> t -> Bool -> v -> v -> H.Expectation
checkAdapter normalize mkAdapter mkContext variants source target lossy vs vt = do
    let cx0 = mkContext variants :: AdapterContext
    let g = adapterContextGraph cx0
    let FlowState adapter' cx trace = unFlow (mkAdapter source) cx0 emptyTrace
    if Y.isNothing adapter' then HL.assertFailure (traceSummary trace) else pure ()
    let adapter = Y.fromJust adapter'
    let step = Coder encode decode
          where
            encode = withState cx . coderEncode (adapterCoder adapter)
            decode = withState cx . coderDecode (adapterCoder adapter)
    adapterSource adapter `H.shouldBe` source
    adapterTarget adapter `H.shouldBe` target
    adapterIsLossy adapter `H.shouldBe` lossy
    fromFlow vt g (normalize <$> coderEncode step vs) `H.shouldBe` (normalize vt)
    if lossy
      then pure ()
      else fromFlow vs g (coderEncode step vs >>= coderDecode step) `H.shouldBe` vs

checkLiteralAdapter :: [LiteralVariant] -> LiteralType -> LiteralType -> Bool -> Literal -> Literal -> H.Expectation
checkLiteralAdapter = checkAdapter id literalAdapter context
  where
    context variants = withConstraints $ (languageConstraints baseLanguage) {
        languageConstraintsLiteralVariants = S.fromList variants,
        languageConstraintsFloatTypes = floatVars,
        languageConstraintsIntegerTypes = integerVars }
      where
        floatVars = S.fromList [FloatTypeFloat32]
        integerVars = S.fromList [IntegerTypeInt16, IntegerTypeInt32]

checkFieldAdapter :: [TypeVariant] -> FieldType -> FieldType -> Bool -> Field -> Field -> H.Expectation
checkFieldAdapter = checkAdapter id fieldAdapter termTestContext

checkFloatAdapter :: [FloatType] -> FloatType -> FloatType -> Bool -> FloatValue -> FloatValue -> H.Expectation
checkFloatAdapter = checkAdapter id floatAdapter context
  where
    context variants = withConstraints $ (languageConstraints baseLanguage) {
      languageConstraintsFloatTypes = S.fromList variants }

checkIntegerAdapter :: [IntegerType] -> IntegerType -> IntegerType -> Bool -> IntegerValue -> IntegerValue -> H.Expectation
checkIntegerAdapter = checkAdapter id integerAdapter context
  where
    context variants = withConstraints $ (languageConstraints baseLanguage) {
      languageConstraintsIntegerTypes = S.fromList variants }

checkDataAdapter :: [TypeVariant] -> Type -> Type -> Bool -> Term -> Term -> H.Expectation
checkDataAdapter = checkAdapter stripTerm termAdapter termTestContext

checkSerdeRoundTrip :: (Type -> Flow Graph (Coder Graph Graph Term BS.ByteString))
  -> TypedTerm -> H.Expectation
checkSerdeRoundTrip mkSerde (TypedTerm typ term) = do
    case mserde of
      Nothing -> HL.assertFailure (traceSummary trace)
      Just serde -> shouldSucceedWith
        (stripTerm <$> (coderEncode serde term >>= coderDecode serde))
        (stripTerm term)
  where
    FlowState mserde _ trace = unFlow (mkSerde typ) testGraph emptyTrace

checkSerialization :: (Type -> Flow Graph (Coder Graph Graph Term String))
  -> TypedTerm -> String -> H.Expectation
checkSerialization mkSerdeStr (TypedTerm typ term) expected = do
    case mserde of
      Nothing -> HL.assertFailure (traceSummary trace)
      Just serde -> shouldSucceedWith
        (normalize <$> coderEncode serde term)
        (normalize expected)
  where
    normalize = unlines . L.filter (not . L.null) . lines
    FlowState mserde _ trace = unFlow (mkSerdeStr typ) testGraph emptyTrace

eval :: Term -> Flow Graph Term
eval = reduceTerm True M.empty

shouldFail :: Show a => Flow Graph a -> H.Expectation
shouldFail = shouldFailIn testGraph

shouldFailIn :: Show a => Graph -> Flow Graph a -> H.Expectation
shouldFailIn g f = case (flowStateValue $ unFlow f g emptyTrace) of
   Nothing -> pure ()
   Just v -> HL.assertFailure $ "Flow should have failed, but suceeeded with " ++ show v

shouldSucceed :: Flow Graph a -> H.Expectation
shouldSucceed = shouldSucceedIn testGraph

shouldSucceedIn :: Graph -> Flow Graph a -> H.Expectation
shouldSucceedIn g f = case my of
    Nothing -> HL.assertFailure (traceSummary trace)
    Just y -> pure ()
  where
    FlowState my _ trace = unFlow f g emptyTrace

shouldSucceedWith :: (Eq a, Show a) => Flow Graph a -> a -> H.Expectation
shouldSucceedWith = shouldSucceedInWith testGraph

shouldSucceedInWith :: (Eq a, Show a) => Graph -> Flow Graph a -> a -> H.Expectation
shouldSucceedInWith g f x = case my of
    Nothing -> HL.assertFailure (traceSummary trace)
    Just y -> y `H.shouldBe` x
  where
    FlowState my _ trace = unFlow f g emptyTrace

strip :: Term -> Term
strip = stripTerm

termTestContext :: [TypeVariant] -> AdapterContext
termTestContext variants = withConstraints $ (languageConstraints baseLanguage) {
    languageConstraintsTypeVariants = S.fromList variants,
    languageConstraintsLiteralVariants = literalVars,
    languageConstraintsFloatTypes = floatVars,
    languageConstraintsIntegerTypes = integerVars }
  where
    literalVars = S.fromList [LiteralVariantFloat, LiteralVariantInteger, LiteralVariantString]
    floatVars = S.fromList [FloatTypeFloat32]
    integerVars = S.fromList [IntegerTypeInt16, IntegerTypeInt32]

withConstraints :: LanguageConstraints -> AdapterContext
withConstraints c = baseContext { adapterContextLanguage = baseLanguage { languageConstraints = c }}
