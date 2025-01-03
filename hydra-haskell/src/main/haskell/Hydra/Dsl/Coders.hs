module Hydra.Dsl.Coders where

import Hydra.Kernel
import Hydra.Dsl.Base as Base
import Hydra.Dsl.Core as Core
import Hydra.Dsl.Lib.Sets as Sets
import Hydra.Dsl.Mantle as Mantle


language
  :: String
  -> [EliminationVariant]
  -> [LiteralVariant]
  -> [FloatType]
  -> [FunctionVariant]
  -> [IntegerType]
  -> [TermVariant]
  -> [TypeVariant]
  -> TTerm (Type -> Bool)
  -> TTerm Language
language name eliminationVariants literalVariants floatTypes functionVariants integerTypes termVariants typeVariants typePredicate = Base.record _Language [
  _Language_name>>: wrap _LanguageName $ string name,
  _Language_constraints>>: Base.record _LanguageConstraints [
    _LanguageConstraints_eliminationVariants>>: Sets.fromList @@ list (Mantle.eliminationVariant <$> eliminationVariants),
    _LanguageConstraints_literalVariants>>: Sets.fromList @@ list (Mantle.literalVariant <$> literalVariants),
    _LanguageConstraints_floatTypes>>: Sets.fromList @@ list (Core.floatType <$> floatTypes),
    _LanguageConstraints_functionVariants>>: Sets.fromList @@ list (Mantle.functionVariant <$> functionVariants),
    _LanguageConstraints_integerTypes>>: Sets.fromList @@ list (Core.integerType <$> integerTypes),
    _LanguageConstraints_termVariants>>: Sets.fromList @@ list (Mantle.termVariant <$> termVariants),
    _LanguageConstraints_typeVariants>>: Sets.fromList @@ list (Mantle.typeVariant <$> typeVariants),
    _LanguageConstraints_types>>: typePredicate]]
