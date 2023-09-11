module Hydra.CoreLanguage where

import qualified Hydra.Basics as Basics
import qualified Hydra.Coders as Coders
import qualified Hydra.Lib.Sets as Sets
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | Language constraints for Java
hydraCoreLanguage :: (Coders.Language a)
hydraCoreLanguage = Coders.Language {
  Coders.languageName = (Coders.LanguageName "hydra/core"),
  Coders.languageConstraints = Coders.LanguageConstraints {
    Coders.languageConstraintsEliminationVariants = (Sets.fromList Basics.eliminationVariants),
    Coders.languageConstraintsLiteralVariants = (Sets.fromList Basics.literalVariants),
    Coders.languageConstraintsFloatTypes = (Sets.fromList Basics.floatTypes),
    Coders.languageConstraintsFunctionVariants = (Sets.fromList Basics.functionVariants),
    Coders.languageConstraintsIntegerTypes = (Sets.fromList Basics.integerTypes),
    Coders.languageConstraintsTermVariants = (Sets.fromList Basics.termVariants),
    Coders.languageConstraintsTypeVariants = (Sets.fromList Basics.typeVariants),
    Coders.languageConstraintsTypes = (\_ -> True)}}