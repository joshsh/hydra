module Hydra.Langs.Protobuf.Language where

import qualified Hydra.Coders as Coders
import qualified Hydra.Core as Core
import qualified Hydra.Lib.Lists as Lists
import qualified Hydra.Lib.Sets as Sets
import qualified Hydra.Mantle as Mantle
import qualified Hydra.Strip as Strip
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | Language constraints for Protocol Buffers v3
protobufLanguage :: (Coders.Language a)
protobufLanguage = Coders.Language {
  Coders.languageName = (Coders.LanguageName "hydra/langs/protobuf"),
  Coders.languageConstraints = Coders.LanguageConstraints {
    Coders.languageConstraintsEliminationVariants = Sets.empty,
    Coders.languageConstraintsLiteralVariants = (Sets.fromList [
      Mantle.LiteralVariantBinary,
      Mantle.LiteralVariantBoolean,
      Mantle.LiteralVariantFloat,
      Mantle.LiteralVariantInteger,
      Mantle.LiteralVariantString]),
    Coders.languageConstraintsFloatTypes = (Sets.fromList [
      Core.FloatTypeFloat32,
      Core.FloatTypeFloat64]),
    Coders.languageConstraintsFunctionVariants = Sets.empty,
    Coders.languageConstraintsIntegerTypes = (Sets.fromList [
      Core.IntegerTypeInt32,
      Core.IntegerTypeInt64,
      Core.IntegerTypeUint32,
      Core.IntegerTypeUint64]),
    Coders.languageConstraintsTermVariants = (Sets.fromList [
      Mantle.TermVariantList,
      Mantle.TermVariantLiteral,
      Mantle.TermVariantMap,
      Mantle.TermVariantOptional,
      Mantle.TermVariantRecord,
      Mantle.TermVariantUnion]),
    Coders.languageConstraintsTypeVariants = (Sets.fromList [
      Mantle.TypeVariantAnnotated,
      Mantle.TypeVariantList,
      Mantle.TypeVariantLiteral,
      Mantle.TypeVariantMap,
      Mantle.TypeVariantOptional,
      Mantle.TypeVariantRecord,
      Mantle.TypeVariantUnion,
      Mantle.TypeVariantVariable]),
    Coders.languageConstraintsTypes = (\x -> case x of
      Core.TypeMap v -> ((\x -> case x of
        Core.TypeOptional _ -> False
        _ -> True) (Strip.stripType (Core.mapTypeValues v)))
      _ -> True)}}

protobufReservedWords :: (Set String)
protobufReservedWords = (Sets.fromList (Lists.concat [
  fieldNames])) 
  where 
    fieldNames = [
      "case",
      "class",
      "data",
      "default",
      "deriving",
      "do",
      "else",
      "foreign",
      "if",
      "import",
      "in",
      "infix",
      "infixl",
      "infixr",
      "instance",
      "let",
      "mdo",
      "module",
      "newtype",
      "of",
      "pattern",
      "proc",
      "rec",
      "then",
      "type",
      "where"]