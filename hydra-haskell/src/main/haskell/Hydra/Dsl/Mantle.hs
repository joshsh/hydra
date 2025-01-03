module Hydra.Dsl.Mantle where

import Hydra.Kernel
import Hydra.Dsl.Base as Base
import Hydra.Dsl.Core

import qualified Data.Map as M
import qualified Data.Maybe as Y


eliminationVariant :: EliminationVariant -> TTerm EliminationVariant
eliminationVariant v = unitVariant _EliminationVariant $ case v of
  EliminationVariantList -> _EliminationVariant_list
  EliminationVariantOptional -> _EliminationVariant_optional
  EliminationVariantProduct -> _EliminationVariant_product
  EliminationVariantRecord -> _EliminationVariant_record
  EliminationVariantUnion -> _EliminationVariant_union
  EliminationVariantWrap -> _EliminationVariant_wrap

functionVariant :: FunctionVariant -> TTerm FunctionVariant
functionVariant v = unitVariant _FunctionVariant $ case v of
  FunctionVariantElimination -> _FunctionVariant_elimination
  FunctionVariantLambda -> _FunctionVariant_lambda
  FunctionVariantPrimitive -> _FunctionVariant_primitive

literalVariant :: LiteralVariant -> TTerm LiteralVariant
literalVariant v = unitVariant _LiteralVariant $ case v of
  LiteralVariantBinary -> _LiteralVariant_binary
  LiteralVariantBoolean -> _LiteralVariant_boolean
  LiteralVariantFloat -> _LiteralVariant_float
  LiteralVariantInteger -> _LiteralVariant_integer
  LiteralVariantString -> _LiteralVariant_string

termAccessorAnnotatedSubject :: TTerm TermAccessor
termAccessorAnnotatedSubject = unitVariant _TermAccessor _TermAccessor_annotatedSubject

termAccessorApplicationFunction :: TTerm TermAccessor
termAccessorApplicationFunction = unitVariant _TermAccessor _TermAccessor_applicationFunction

termAccessorApplicationArgument :: TTerm TermAccessor
termAccessorApplicationArgument = unitVariant _TermAccessor _TermAccessor_applicationArgument

termAccessorLambdaBody :: TTerm TermAccessor
termAccessorLambdaBody = unitVariant _TermAccessor _TermAccessor_lambdaBody

termAccessorListFold :: TTerm TermAccessor
termAccessorListFold = unitVariant _TermAccessor _TermAccessor_listFold

termAccessorOptionalCasesNothing :: TTerm TermAccessor
termAccessorOptionalCasesNothing = unitVariant _TermAccessor _TermAccessor_optionalCasesNothing

termAccessorOptionalCasesJust :: TTerm TermAccessor
termAccessorOptionalCasesJust = unitVariant _TermAccessor _TermAccessor_optionalCasesJust

termAccessorUnionCasesDefault :: TTerm TermAccessor
termAccessorUnionCasesDefault = unitVariant _TermAccessor _TermAccessor_unionCasesDefault

termAccessorUnionCasesBranch :: TTerm Name -> TTerm TermAccessor
termAccessorUnionCasesBranch = variant _TermAccessor _TermAccessor_unionCasesBranch

termAccessorLetEnvironment :: TTerm TermAccessor
termAccessorLetEnvironment = unitVariant _TermAccessor _TermAccessor_letEnvironment

termAccessorLetBinding :: TTerm Name -> TTerm TermAccessor
termAccessorLetBinding = variant _TermAccessor _TermAccessor_letBinding

termAccessorListElement :: TTerm Int -> TTerm TermAccessor
termAccessorListElement = variant _TermAccessor _TermAccessor_listElement

termAccessorMapKey :: TTerm Int -> TTerm TermAccessor
termAccessorMapKey = variant _TermAccessor _TermAccessor_mapKey

termAccessorMapValue :: TTerm Int -> TTerm TermAccessor
termAccessorMapValue = variant _TermAccessor _TermAccessor_mapValue

termAccessorOptionalTerm :: TTerm TermAccessor
termAccessorOptionalTerm = unitVariant _TermAccessor _TermAccessor_optionalTerm

termAccessorProductTerm :: TTerm Int -> TTerm TermAccessor
termAccessorProductTerm = variant _TermAccessor _TermAccessor_productTerm

termAccessorRecordField :: TTerm Name -> TTerm TermAccessor
termAccessorRecordField = variant _TermAccessor _TermAccessor_recordField

termAccessorSetElement :: TTerm Int -> TTerm TermAccessor
termAccessorSetElement = variant _TermAccessor _TermAccessor_setElement

termAccessorSumTerm :: TTerm TermAccessor
termAccessorSumTerm = unitVariant _TermAccessor _TermAccessor_sumTerm

termAccessorTypeAbstractionBody :: TTerm TermAccessor
termAccessorTypeAbstractionBody = unitVariant _TermAccessor _TermAccessor_typeAbstractionBody

termAccessorTypeApplicationTerm :: TTerm TermAccessor
termAccessorTypeApplicationTerm = unitVariant _TermAccessor _TermAccessor_typeApplicationTerm

termAccessorTypedTerm :: TTerm TermAccessor
termAccessorTypedTerm = unitVariant _TermAccessor _TermAccessor_typedTerm

termAccessorInjectionTerm :: TTerm TermAccessor
termAccessorInjectionTerm = unitVariant _TermAccessor _TermAccessor_injectionTerm

termAccessorWrappedTerm :: TTerm TermAccessor
termAccessorWrappedTerm = unitVariant _TermAccessor _TermAccessor_wrappedTerm

termVariant :: TermVariant -> TTerm TermVariant
termVariant v = unitVariant _TermVariant $ case v of
  TermVariantAnnotated -> _TermVariant_annotated
  TermVariantApplication -> _TermVariant_application
  TermVariantFunction -> _TermVariant_function
  TermVariantLet -> _TermVariant_let
  TermVariantList -> _TermVariant_list
  TermVariantLiteral -> _TermVariant_literal
  TermVariantMap -> _TermVariant_map
  TermVariantOptional -> _TermVariant_optional
  TermVariantProduct -> _TermVariant_product
  TermVariantRecord -> _TermVariant_record
  TermVariantSet -> _TermVariant_set
  TermVariantSum -> _TermVariant_sum
  TermVariantTypeAbstraction -> _TermVariant_typeAbstraction
  TermVariantTypeApplication -> _TermVariant_typeApplication
  TermVariantTyped -> _TermVariant_typed
  TermVariantUnion -> _TermVariant_union
  TermVariantVariable -> _TermVariant_variable
  TermVariantWrap -> _TermVariant_wrap

typeVariant :: TypeVariant -> TTerm TypeVariant
typeVariant v = unitVariant _TypeVariant $ case v of
  TypeVariantAnnotated -> _TypeVariant_annotated
  TypeVariantApplication -> _TypeVariant_application
  TypeVariantFunction -> _TypeVariant_function
  TypeVariantLambda -> _TypeVariant_lambda
  TypeVariantList -> _TypeVariant_list
  TypeVariantLiteral -> _TypeVariant_literal
  TypeVariantMap -> _TypeVariant_map
  TypeVariantOptional -> _TypeVariant_optional
  TypeVariantProduct -> _TypeVariant_product
  TypeVariantRecord -> _TypeVariant_record
  TypeVariantSet -> _TypeVariant_set
  TypeVariantUnion -> _TypeVariant_union
  TypeVariantVariable -> _TypeVariant_variable
