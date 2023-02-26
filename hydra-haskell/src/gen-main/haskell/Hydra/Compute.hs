-- | Abstractions for evaluation and transformations

module Hydra.Compute where

import qualified Hydra.Core as Core
import qualified Hydra.Graph as Graph
import qualified Hydra.Mantle as Mantle
import Data.List
import Data.Map
import Data.Set

-- | A two-level bidirectional encoder which adapts types to types and terms to terms
data Adapter s1 s2 t1 t2 v1 v2 = 
  Adapter {
    adapterIsLossy :: Bool,
    adapterSource :: t1,
    adapterTarget :: t2,
    adapterCoder :: (Coder s1 s2 v1 v2)}

_Adapter = (Core.Name "hydra/compute.Adapter")

_Adapter_isLossy = (Core.FieldName "isLossy")

_Adapter_source = (Core.FieldName "source")

_Adapter_target = (Core.FieldName "target")

_Adapter_coder = (Core.FieldName "coder")

-- | An evaluation context together with a source language and a target language
data AdapterContext m = 
  AdapterContext {
    adapterContextEvaluation :: (Context m),
    adapterContextSource :: (Language m),
    adapterContextTarget :: (Language m)}

_AdapterContext = (Core.Name "hydra/compute.AdapterContext")

_AdapterContext_evaluation = (Core.FieldName "evaluation")

_AdapterContext_source = (Core.FieldName "source")

_AdapterContext_target = (Core.FieldName "target")

-- | A typeclass-like construct providing common functions for working with annotations
data AnnotationClass m = 
  AnnotationClass {
    annotationClassDefault :: m,
    annotationClassEqual :: (m -> m -> Bool),
    annotationClassCompare :: (m -> m -> Mantle.Comparison),
    annotationClassShow :: (m -> String),
    annotationClassRead :: (String -> Maybe m),
    annotationClassTermAnnotation :: (Core.Term m -> m),
    annotationClassTypeAnnotation :: (Core.Type m -> m),
    annotationClassTermDescription :: (Core.Term m -> Flow (Context m) (Maybe String)),
    annotationClassTypeDescription :: (Core.Type m -> Flow (Context m) (Maybe String)),
    annotationClassTermType :: (Core.Term m -> Flow (Context m) (Maybe (Core.Type m))),
    annotationClassSetTermDescription :: (Context m -> Maybe String -> Core.Term m -> Core.Term m),
    annotationClassSetTermType :: (Context m -> Maybe (Core.Type m) -> Core.Term m -> Core.Term m),
    annotationClassTypeOf :: (m -> Flow (Context m) (Maybe (Core.Type m))),
    annotationClassSetTypeOf :: (Maybe (Core.Type m) -> m -> m)}

_AnnotationClass = (Core.Name "hydra/compute.AnnotationClass")

_AnnotationClass_default = (Core.FieldName "default")

_AnnotationClass_equal = (Core.FieldName "equal")

_AnnotationClass_compare = (Core.FieldName "compare")

_AnnotationClass_show = (Core.FieldName "show")

_AnnotationClass_read = (Core.FieldName "read")

_AnnotationClass_termAnnotation = (Core.FieldName "termAnnotation")

_AnnotationClass_typeAnnotation = (Core.FieldName "typeAnnotation")

_AnnotationClass_termDescription = (Core.FieldName "termDescription")

_AnnotationClass_typeDescription = (Core.FieldName "typeDescription")

_AnnotationClass_termType = (Core.FieldName "termType")

_AnnotationClass_setTermDescription = (Core.FieldName "setTermDescription")

_AnnotationClass_setTermType = (Core.FieldName "setTermType")

_AnnotationClass_typeOf = (Core.FieldName "typeOf")

_AnnotationClass_setTypeOf = (Core.FieldName "setTypeOf")

-- | An encoder and decoder; a bidirectional flow between two types
data Coder s1 s2 v1 v2 = 
  Coder {
    coderEncode :: (v1 -> Flow s1 v2),
    coderDecode :: (v2 -> Flow s2 v1)}

_Coder = (Core.Name "hydra/compute.Coder")

_Coder_encode = (Core.FieldName "encode")

_Coder_decode = (Core.FieldName "decode")

-- | Indicates either the 'out' or the 'in' direction of a coder
data CoderDirection = 
  CoderDirectionEncode  |
  CoderDirectionDecode 
  deriving (Eq, Ord, Read, Show)

_CoderDirection = (Core.Name "hydra/compute.CoderDirection")

_CoderDirection_encode = (Core.FieldName "encode")

_CoderDirection_decode = (Core.FieldName "decode")

-- | An environment containing a graph together with primitive functions and other necessary components for evaluation
data Context m = 
  Context {
    -- | The lambda environment of this graph context; it indicates whether a variable is bound by a lambda (Nothing) or a let (Just term)
    contextEnvironment :: (Map Core.Name (Maybe (Core.Term m))),
    -- | The body of the term which generated this context
    contextBody :: (Core.Term m),
    -- | The graph itself
    contextGraph :: (Graph.Graph m),
    -- | All supported primitive constants and functions, by name
    contextPrimitives :: (Map Core.Name (Primitive m)),
    -- | The annotation class which is supported in this context
    contextAnnotations :: (AnnotationClass m),
    -- | The schema of this graph. If this parameter is omitted (nothing), the graph is its own schema graph.
    contextSchema :: (Maybe (Context m))}

_Context = (Core.Name "hydra/compute.Context")

_Context_environment = (Core.FieldName "environment")

_Context_body = (Core.FieldName "body")

_Context_graph = (Core.FieldName "graph")

_Context_primitives = (Core.FieldName "primitives")

_Context_annotations = (Core.FieldName "annotations")

_Context_schema = (Core.FieldName "schema")

-- | A variant of the State monad with built-in logging and error handling
newtype Flow s a = 
  Flow {
    unFlow :: (s -> Trace -> FlowState s a)}

_Flow = (Core.Name "hydra/compute.Flow")

-- | The result of evaluating a Flow
data FlowState s a = 
  FlowState {
    flowStateValue :: (Maybe a),
    flowStateState :: s,
    flowStateTrace :: Trace}
  deriving (Eq, Ord, Read, Show)

_FlowState = (Core.Name "hydra/compute.FlowState")

_FlowState_value = (Core.FieldName "value")

_FlowState_state = (Core.FieldName "state")

_FlowState_trace = (Core.FieldName "trace")

-- | A key/value map which serves as a built-in metadata container for terms
data Kv = 
  Kv {
    -- | A map of annotation names to annotation values
    kvAnnotations :: (Map String (Core.Term Kv))}
  deriving (Eq, Ord, Read, Show)

_Kv = (Core.Name "hydra/compute.Kv")

_Kv_annotations = (Core.FieldName "annotations")

-- | A named language together with language-specific constraints
data Language m = 
  Language {
    languageName :: LanguageName,
    languageConstraints :: (LanguageConstraints m)}

_Language = (Core.Name "hydra/compute.Language")

_Language_name = (Core.FieldName "name")

_Language_constraints = (Core.FieldName "constraints")

-- | A set of constraints on valid type and term expressions, characterizing a language
data LanguageConstraints m = 
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
    languageConstraintsTypes :: (Core.Type m -> Bool)}

_LanguageConstraints = (Core.Name "hydra/compute.LanguageConstraints")

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

_LanguageName = (Core.Name "hydra/compute.LanguageName")

-- | A built-in function
data Primitive m = 
  Primitive {
    -- | The unique name of the primitive function
    primitiveName :: Core.Name,
    -- | The type signature of the primitive function
    primitiveType :: (Core.Type m),
    -- | A concrete implementation of the primitive function
    primitiveImplementation :: ([Core.Term m] -> Flow () (Core.Term m))}

_Primitive = (Core.Name "hydra/compute.Primitive")

_Primitive_name = (Core.FieldName "name")

_Primitive_type = (Core.FieldName "type")

_Primitive_implementation = (Core.FieldName "implementation")

-- | A type together with a coder for mapping terms into arguments for primitive functions, and mapping computed results into terms
data TermCoder m a = 
  TermCoder {
    termCoderType :: (Core.Type m),
    termCoderCoder :: (Coder () () (Core.Term m) a)}

_TermCoder = (Core.Name "hydra/compute.TermCoder")

_TermCoder_type = (Core.FieldName "type")

_TermCoder_coder = (Core.FieldName "coder")

-- | A container for logging and error information
data Trace = 
  Trace {
    traceStack :: [String],
    traceMessages :: [String],
    -- | A map of string keys to arbitrary terms as values, for application-specific use
    traceOther :: (Map String (Core.Term Kv))}
  deriving (Eq, Ord, Read, Show)

_Trace = (Core.Name "hydra/compute.Trace")

_Trace_stack = (Core.FieldName "stack")

_Trace_messages = (Core.FieldName "messages")

_Trace_other = (Core.FieldName "other")

-- | Specifies either a pre-order or post-order traversal
data TraversalOrder = 
  -- | Pre-order traversal
  TraversalOrderPre  |
  -- | Post-order traversal
  TraversalOrderPost 
  deriving (Eq, Ord, Read, Show)

_TraversalOrder = (Core.Name "hydra/compute.TraversalOrder")

_TraversalOrder_pre = (Core.FieldName "pre")

_TraversalOrder_post = (Core.FieldName "post")