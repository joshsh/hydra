-- | Abstractions for paired transformations between languages

module Hydra.Coders where

import qualified Hydra.Compute as Compute
import qualified Hydra.Core as Core
import qualified Hydra.Graph as Graph
import qualified Hydra.Mantle as Mantle
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

-- | An evaluation context together with a source language and a target language
data AdapterContext a = 
  AdapterContext {
    adapterContextGraph :: (Graph.Graph Core.Kv),
    adapterContextLanguage :: (Language Core.Kv),
    adapterContextAdapters :: (Map Core.Name (Compute.Adapter (AdapterContext Core.Kv) (AdapterContext Core.Kv) (Core.Type Core.Kv) (Core.Type Core.Kv) (Core.Term Core.Kv) (Core.Term Core.Kv)))}

_AdapterContext = (Core.Name "hydra/coders.AdapterContext")

_AdapterContext_graph = (Core.FieldName "graph")

_AdapterContext_language = (Core.FieldName "language")

_AdapterContext_adapters = (Core.FieldName "adapters")

-- | Indicates either the 'out' or the 'in' direction of a coder
data CoderDirection = 
  CoderDirectionEncode  |
  CoderDirectionDecode 
  deriving (Eq, Ord, Read, Show)

_CoderDirection = (Core.Name "hydra/coders.CoderDirection")

_CoderDirection_encode = (Core.FieldName "encode")

_CoderDirection_decode = (Core.FieldName "decode")

-- | A named language together with language-specific constraints
data Language a = 
  Language {
    languageName :: LanguageName,
    languageConstraints :: (LanguageConstraints a)}

_Language = (Core.Name "hydra/coders.Language")

_Language_name = (Core.FieldName "name")

_Language_constraints = (Core.FieldName "constraints")

-- | A set of constraints on valid type and term expressions, characterizing a language
data LanguageConstraints a = 
  LanguageConstraints {
    -- | All supported elimination variants
    languageConstraintsEliminationVariants :: (Set Mantle.EliminationVariant),
    -- | All supported literal variants
    languageConstraintsLiteralVariants :: (Set Mantle.LiteralVariant),
    -- | All supported float types
    languageConstraintsFloatTypes :: (Set Core.FloatType),
    -- | All supported function variants
    languageConstraintsFunctionVariants :: (Set Mantle.FunctionVariant),
    -- | All supported integer types
    languageConstraintsIntegerTypes :: (Set Core.IntegerType),
    -- | All supported term variants
    languageConstraintsTermVariants :: (Set Mantle.TermVariant),
    -- | All supported type variants
    languageConstraintsTypeVariants :: (Set Mantle.TypeVariant),
    -- | A logical set of types, as a predicate which tests a type for inclusion
    languageConstraintsTypes :: (Core.Type Core.Kv -> Bool)}

_LanguageConstraints = (Core.Name "hydra/coders.LanguageConstraints")

_LanguageConstraints_eliminationVariants = (Core.FieldName "eliminationVariants")

_LanguageConstraints_literalVariants = (Core.FieldName "literalVariants")

_LanguageConstraints_floatTypes = (Core.FieldName "floatTypes")

_LanguageConstraints_functionVariants = (Core.FieldName "functionVariants")

_LanguageConstraints_integerTypes = (Core.FieldName "integerTypes")

_LanguageConstraints_termVariants = (Core.FieldName "termVariants")

_LanguageConstraints_typeVariants = (Core.FieldName "typeVariants")

_LanguageConstraints_types = (Core.FieldName "types")

-- | The unique name of a language
newtype LanguageName = 
  LanguageName {
    -- | The unique name of a language
    unLanguageName :: String}
  deriving (Eq, Ord, Read, Show)

_LanguageName = (Core.Name "hydra/coders.LanguageName")

-- | Specifies either a pre-order or post-order traversal
data TraversalOrder = 
  -- | Pre-order traversal
  TraversalOrderPre  |
  -- | Post-order traversal
  TraversalOrderPost 
  deriving (Eq, Ord, Read, Show)

_TraversalOrder = (Core.Name "hydra/coders.TraversalOrder")

_TraversalOrder_pre = (Core.FieldName "pre")

_TraversalOrder_post = (Core.FieldName "post")
