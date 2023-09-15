-- | Additional adapter utilities, above and beyond the generated ones

module Hydra.AdapterUtils (
  module Hydra.AdapterUtils,
  module Hydra.Printing,
) where

import Hydra.Coders
import Hydra.Compute
import Hydra.Core
import Hydra.Basics
import Hydra.Module
import Hydra.Printing
import Hydra.Mantle
import Hydra.Kv
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms

import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Maybe as Y
import Control.Monad


type SymmetricAdapter s t v = Adapter s s t t v v

type TypeAdapter a = Type Kv -> Flow (AdapterContext Kv) (SymmetricAdapter (AdapterContext Kv) (Type Kv) (Term Kv))

bidirectional :: (CoderDirection -> b -> Flow s b) -> Coder s s b b
bidirectional f = Coder (f CoderDirectionEncode) (f CoderDirectionDecode)

chooseAdapter :: (Eq t, Ord t, Show t) =>
    (t -> [Flow so (SymmetricAdapter si t v)])
 -> (t -> Bool)
 -> (t -> String)
 -> t
 -> Flow so (SymmetricAdapter si t v)
chooseAdapter alts supported describe typ = if supported typ
  then pure $ Adapter False typ typ idCoder
  else do
    -- Uncomment to debug adapter cycles
    -- debugCheckType typ

    raw <- sequence (alts typ)
    let candidates = L.filter (supported . adapterTarget) raw
    if L.null candidates
      then fail $ "no adapters found for " ++ describe typ
        ++ (if L.null raw
           then ""
           else " (discarded " ++ show (L.length raw) ++ " unsupported candidate types: " ++ show (adapterTarget <$> raw) ++ ")")
        ++ ". Original type: " ++ show typ
      else do
        -- Uncomment to debug adapter cycles
        -- debugRemoveType typ

        return $ L.head candidates

composeCoders :: Coder s s a b -> Coder s s b c -> Coder s s a c
composeCoders c1 c2 = Coder {
  coderEncode = coderEncode c1 >=> coderEncode c2,
  coderDecode = coderDecode c2 >=> coderDecode c1}

debugCheckType :: (Eq t, Ord t, Show t) => t -> Flow s ()
debugCheckType typ = do
  let s = show typ
  types <- getAttrWithDefault "types" (Terms.set S.empty) >>= Expect.set Expect.string
  if S.member s types
    then fail $ "detected a cycle; type has already been encountered: " ++ show typ
    else putAttr "types" $ Terms.set $ S.fromList (Terms.string <$> (S.toList $ S.insert s types))
  return ()

debugRemoveType :: (Eq t, Ord t, Show t) => t -> Flow s ()
debugRemoveType typ = do
  let s = show typ
  types <- getAttrWithDefault "types" (Terms.set S.empty) >>= Expect.set Expect.string
  let types' = S.delete s types
  putAttr "types" $ Terms.set $ S.fromList (Terms.string <$> (S.toList $ S.insert s types'))

encodeDecode :: CoderDirection -> Coder s s x x -> x -> Flow s x
encodeDecode dir = case dir of
  CoderDirectionEncode -> coderEncode
  CoderDirectionDecode -> coderDecode

floatTypeIsSupported :: LanguageConstraints a -> FloatType -> Bool
floatTypeIsSupported constraints ft = S.member ft $ languageConstraintsFloatTypes constraints

idAdapter :: t -> SymmetricAdapter s t v
idAdapter t = Adapter False t t idCoder

idCoder :: Coder s s a a
idCoder = Coder pure pure

integerTypeIsSupported :: LanguageConstraints a -> IntegerType -> Bool
integerTypeIsSupported constraints it = S.member it $ languageConstraintsIntegerTypes constraints

literalTypeIsSupported :: LanguageConstraints a -> LiteralType -> Bool
literalTypeIsSupported constraints at = S.member (literalTypeVariant at) (languageConstraintsLiteralVariants constraints)
  && case at of
    LiteralTypeFloat ft -> floatTypeIsSupported constraints ft
    LiteralTypeInteger it -> integerTypeIsSupported constraints it
    _ -> True

nameToFilePath :: Bool -> FileExtension -> Name -> FilePath
nameToFilePath caps ext name = namespaceToFilePath caps ext $ Namespace $ prefix ++ local
  where
    QualifiedName ns local = qualifyNameEager name
    prefix = Y.maybe "" (\(Namespace gname) -> gname ++ "/") ns

typeIsSupported :: LanguageConstraints a -> Type Kv -> Bool
typeIsSupported constraints t = languageConstraintsTypes constraints t -- these are *additional* type constraints
  && isSupportedVariant (typeVariant t)
  && case t of
    TypeAnnotated (Annotated at _) -> typeIsSupported constraints at
    TypeLiteral at -> literalTypeIsSupported constraints at
    TypeFunction (FunctionType dom cod) -> typeIsSupported constraints dom && typeIsSupported constraints cod
    TypeList lt -> typeIsSupported constraints lt
    TypeMap (MapType kt vt) -> typeIsSupported constraints kt && typeIsSupported constraints vt
    TypeWrap _ -> True -- TODO: dereference the type
    TypeOptional t -> typeIsSupported constraints t
    TypeRecord rt -> and $ typeIsSupported constraints . fieldTypeType <$> rowTypeFields rt
    TypeSet st -> typeIsSupported constraints st
    TypeUnion rt -> and $ typeIsSupported constraints . fieldTypeType <$> rowTypeFields rt
    _ -> True
  where
    isSupportedVariant v = v == TypeVariantVariable || S.member v (languageConstraintsTypeVariants constraints)

unidirectionalCoder :: (a -> Flow s b) -> Coder s s a b
unidirectionalCoder m = Coder {
  coderEncode = m,
  coderDecode = \_ -> fail "inbound mapping is unsupported"}
