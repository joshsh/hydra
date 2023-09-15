{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier2.CoreLanguage where

-- Standard Tier-2 imports
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
import           Hydra.Sources.Tier1.All

import Hydra.Sources.Tier2.Basics


hydraCoreLanguageModule :: Module Kv
hydraCoreLanguageModule = Module ns elements [hydraBasicsModule] Nothing
  where
    ns = Namespace "hydra/coreLanguage"
    elements = [el hydraCoreLanguageDef]

hydraCoreLanguageDef :: Definition (Language Kv)
hydraCoreLanguageDef = definitionInModule hydraCoreLanguageModule "hydraCoreLanguage" $
  doc "Language constraints for Java" $
  typed languageA $
  record _Language [
    _Language_name>>: wrap _LanguageName "hydra/core",
    _Language_constraints>>: record _LanguageConstraints [
    _LanguageConstraints_eliminationVariants>>: Sets.fromList @@ ref eliminationVariantsDef,
    _LanguageConstraints_literalVariants>>: Sets.fromList @@ ref literalVariantsDef,
    _LanguageConstraints_floatTypes>>: Sets.fromList @@ ref floatTypesDef,
    _LanguageConstraints_functionVariants>>: Sets.fromList @@ ref functionVariantsDef,
    _LanguageConstraints_integerTypes>>: Sets.fromList @@ ref integerTypesDef,
    _LanguageConstraints_termVariants>>: Sets.fromList @@ ref termVariantsDef,
    _LanguageConstraints_typeVariants>>: Sets.fromList @@ ref typeVariantsDef,
    _LanguageConstraints_types>>: constant true]]
