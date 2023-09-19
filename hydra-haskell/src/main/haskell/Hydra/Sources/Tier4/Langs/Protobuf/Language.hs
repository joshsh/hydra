{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Langs.Protobuf.Language (protobufLanguageModule) where

-- Standard Tier-4 imports
import           Prelude hiding ((++))
import qualified Data.List                 as L
import qualified Data.Map                  as M
import qualified Data.Set                  as S
import qualified Data.Maybe                as Y
import           Hydra.Dsl.Base            as Base
import qualified Hydra.Dsl.Core            as Core
import qualified Hydra.Dsl.Graph           as Graph
import qualified Hydra.Dsl.Lib.Equality    as Equality
import qualified Hydra.Dsl.Lib.Flows       as Flows
import qualified Hydra.Dsl.Lib.Io          as Io
import qualified Hydra.Dsl.Lib.Lists       as Lists
import qualified Hydra.Dsl.Lib.Literals    as Literals
import qualified Hydra.Dsl.Lib.Logic       as Logic
import qualified Hydra.Dsl.Lib.Maps        as Maps
import qualified Hydra.Dsl.Lib.Math        as Math
import qualified Hydra.Dsl.Lib.Optionals   as Optionals
import qualified Hydra.Dsl.Lib.Sets        as Sets
import           Hydra.Dsl.Lib.Strings     as Strings
import qualified Hydra.Dsl.Module          as Module
import qualified Hydra.Dsl.Terms           as Terms
import qualified Hydra.Dsl.Types           as Types
import           Hydra.Sources.Tier3.All


protobufLanguageDefinition :: String -> Datum a -> Definition a
protobufLanguageDefinition = definitionInModule protobufLanguageModule

protobufLanguageModule :: Module
protobufLanguageModule = Module ns elements [hydraCodersModule, hydraBasicsModule, hydraStripModule] Nothing
  where
    ns = Namespace "hydra/langs/protobuf/language"
    elements = [
      el protobufLanguageDef,
      el protobufReservedWordsDef]

protobufLanguageDef :: Definition Language
protobufLanguageDef = protobufLanguageDefinition "protobufLanguage" $
  doc "Language constraints for Protocol Buffers v3" $
  record _Language [
    _Language_name>>: wrap _LanguageName "hydra/langs/protobuf",
    _Language_constraints>>: record _LanguageConstraints [
      _LanguageConstraints_eliminationVariants>>: Sets.empty,
      _LanguageConstraints_literalVariants>>: Sets.fromList @@ list (unitVariant _LiteralVariant <$> [
        _LiteralVariant_binary,
        _LiteralVariant_boolean,
        _LiteralVariant_float,
        _LiteralVariant_integer,
        _LiteralVariant_string]),
      _LanguageConstraints_floatTypes>>: Sets.fromList @@ list (unitVariant _FloatType <$> [
        _FloatType_float32,
        _FloatType_float64]),
      _LanguageConstraints_functionVariants>>: Sets.empty,
      _LanguageConstraints_integerTypes>>: Sets.fromList @@ list (unitVariant _IntegerType <$> [
        _IntegerType_int32,
        _IntegerType_int64,
        _IntegerType_uint32,
        _IntegerType_uint64]),
      _LanguageConstraints_termVariants>>: Sets.fromList @@ list (unitVariant _TermVariant <$> [
        _TermVariant_list,
        _TermVariant_literal,
        _TermVariant_map,
        _TermVariant_optional,
        _TermVariant_record,
        _TermVariant_union]),
      _LanguageConstraints_typeVariants>>: Sets.fromList @@ list (unitVariant _TypeVariant <$> [
        _TypeVariant_annotated,
        _TypeVariant_list,
        _TypeVariant_literal,
        _TypeVariant_map,
        _TypeVariant_optional,
        _TypeVariant_record,
        _TypeVariant_union,
        _TypeVariant_variable]),
      _LanguageConstraints_types>>: match _Type (Just true) [
        _Type_map>>: lambda "mt" (match _Type (Just true) [
          _Type_optional>>: constant false] @@ (ref stripTypeDef @@ (Core.mapTypeValues @@ var "mt")))]]]

protobufReservedWordsDef :: Definition (S.Set String)
protobufReservedWordsDef = protobufLanguageDefinition "protobufReservedWords" $
  doc "A set of reserved words in Protobuf" $
  (Sets.fromList @@ (Lists.concat @@ list [var "fieldNames"]))
  `with` [
    "fieldNames">:
      doc "See: http://google.github.io/proto-lens/reserved-names.html" $
      list [
        "case", "class", "data", "default", "deriving", "do", "else", "foreign", "if", "import", "in", "infix", "infixl",
        "infixr", "instance", "let", "mdo", "module", "newtype", "of", "pattern", "proc", "rec", "then", "type", "where"]]
