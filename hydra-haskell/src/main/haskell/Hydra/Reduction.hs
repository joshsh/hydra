-- | Functions for reducing terms and types, i.e. performing computations

module Hydra.Reduction where

import Hydra.Basics
import Hydra.Strip
import Hydra.Compute
import Hydra.Core
import Hydra.Schemas
import Hydra.Extras
import Hydra.Graph
import Hydra.Kv
import Hydra.Lexical
import Hydra.Rewriting
import Hydra.Tier1
import Hydra.Tier2
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


-- For demo purposes. This should be generalized to enable additional side effects of interest.
countPrimitiveInvocations :: Bool
countPrimitiveInvocations = True

-- A term evaluation function which is alternatively lazy or eager
reduceTerm :: Bool -> M.Map Name Term -> Term -> Flow Graph Term
reduceTerm eager env = rewriteTermM mapping
  where
    reduce eager = reduceTerm eager M.empty

    mapping recurse mid = do
      inner <- if doRecurse eager mid then recurse mid else pure mid
      applyIfNullary eager inner []

    doRecurse eager term = eager && case term of
      TermFunction (FunctionLambda _) -> False
      _ -> True

    -- Reduce an argument only if evaluation is lazy (i.e. the argument may not already have been reduced)
    reduceArg eager arg = if eager then pure arg else reduce False arg

    applyToArguments fun args = case args of
      [] -> fun
      (h:r) -> applyToArguments (Terms.apply fun h) r

    replaceFreeName toReplace replacement = rewriteTerm mapping
      where
        mapping recurse inner = case inner of
          TermFunction (FunctionLambda (Lambda param _ body)) -> if param == toReplace then inner else recurse inner
          TermVariable name -> if name == toReplace then replacement else inner
          _ -> recurse inner

    applyIfNullary eager original args = case stripTerm original of
      TermApplication (Application fun arg) -> applyIfNullary eager fun (arg:args)
      TermFunction fun -> case fun of
        FunctionElimination elm -> case args of
          [] -> pure original
          -- Reduce the argument prior to application, regardless of laziness
          (arg:remainingArgs) -> do
            reducedArg <- reduceArg eager $ stripTerm arg
            reducedResult <- applyElimination elm reducedArg >>= reduce eager
            applyIfNullary eager reducedResult remainingArgs
        FunctionLambda (Lambda param _ body) -> case args of
          [] -> pure original
          (arg:remainingArgs) -> do
            reducedArg <- reduce eager $ stripTerm arg
            reducedResult <- reduce eager $ replaceFreeName param reducedArg body
            applyIfNullary eager reducedResult remainingArgs
        FunctionPrimitive name -> do
          prim <- requirePrimitive name
          let arity = primitiveArity prim
          if arity > L.length args
            -- Not enough arguments available; back out
            then return $ applyToArguments original args
            else do
              let argList = L.take arity args
              let remainingArgs = L.drop arity args
              reducedArgs <- CM.mapM (reduceArg eager) argList
              reducedResult <- primitiveImplementation prim reducedArgs >>= reduce eager
              applyIfNullary eager reducedResult remainingArgs
      TermVariable _ -> pure $ applyToArguments original args -- TODO: dereference variables
      _ -> pure $ applyToArguments original args

    applyElimination elm reducedArg = case elm of
      EliminationList _ -> fail "list eliminations are unsupported"
      EliminationOptional _ -> fail "optional eliminations are unsupported"
      EliminationRecord proj -> do
        fields <- Expect.recordWithName (projectionTypeName proj) $ stripTerm reducedArg
        let matchingFields = L.filter (\f -> fieldName f == projectionField proj) fields
        if L.null matchingFields
          then fail $ "no such field: " ++ unFieldName (projectionField proj) ++ " in " ++ unName (projectionTypeName proj) ++ " record"
          else pure $ fieldTerm $ L.head matchingFields
      EliminationUnion (CaseStatement name def fields) -> do
        field <- Expect.injectionWithName name reducedArg
        let matchingFields = L.filter (\f -> fieldName f == fieldName field) fields
        if L.null matchingFields
          then case def of
            Just d -> pure d
            Nothing -> fail $ "no such field " ++ unFieldName (fieldName field) ++ " in " ++ unName name ++ " case statement"
          else pure $ Terms.apply (fieldTerm $ L.head matchingFields) (fieldTerm field)
      EliminationWrap name -> Expect.wrap name reducedArg

-- Note: this is eager beta reduction, in that we always descend into subtypes,
--       and always reduce the right-hand side of an application prior to substitution
betaReduceType :: Type -> Flow Graph Type
betaReduceType typ = do
    g <- getState :: Flow Graph Graph
    rewriteTypeM mapExpr typ
  where
    mapExpr recurse t = do
        r <- recurse t
        case r of
          TypeApplication a -> reduceApp a
          t' -> pure t'
      where
        reduceApp (ApplicationType lhs rhs) = case lhs of
          TypeAnnotated (Annotated t' ann) -> do
            a <- reduceApp $ ApplicationType t' rhs
            return $ TypeAnnotated $ Annotated a ann
          TypeLambda (LambdaType v body) -> betaReduceType $ replaceFreeName v rhs body
          -- nominal types are transparent
          TypeVariable name -> do
            t' <- requireType name
            betaReduceType $ TypeApplication $ ApplicationType t' rhs

-- | Apply the special rules:
--     ((\x.e1) e2) == e1, where x does not appear free in e1
--   and
--     ((\x.e1) e2) = e1[x/e2]
--  These are both limited forms of beta reduction which help to "clean up" a term without fully evaluating it.
contractTerm :: Term -> Term
contractTerm = rewriteTerm rewrite
  where
    rewrite recurse term = case rec of
        TermApplication (Application lhs rhs) -> case stripTerm lhs of
          TermFunction (FunctionLambda (Lambda v _ body)) -> if isFreeIn v body
            then body
            else alphaConvertTerm v rhs body
          _ -> rec
        _ -> rec
      where
        rec = recurse term

-- Note: unused / untested
etaReduceTerm :: Term -> Term
etaReduceTerm term = case term of
    TermAnnotated (Annotated term1 ann) -> TermAnnotated (Annotated (etaReduceTerm term1) ann)
    TermFunction (FunctionLambda l) -> reduceLambda l
    _ -> noChange
  where
    reduceLambda (Lambda v dom body) = case etaReduceTerm body of
      TermAnnotated (Annotated body1 ann) -> reduceLambda (Lambda v dom body1)
      TermApplication a -> reduceApplication a
        where
          reduceApplication (Application lhs rhs) = case etaReduceTerm rhs of
            TermAnnotated (Annotated rhs1 ann) -> reduceApplication (Application lhs rhs1)
            TermVariable v1 -> if v == v1 && isFreeIn v lhs
              then etaReduceTerm lhs
              else noChange
            _ -> noChange
      _ -> noChange
    noChange = term

-- | Whether a term is closed, i.e. represents a complete program
termIsClosed :: Term -> Bool
termIsClosed = S.null . freeVariablesInTerm

-- | Whether a term has been fully reduced to a "value"
termIsValue :: Graph -> Term -> Bool
termIsValue g term = case stripTerm term of
    TermApplication _ -> False
    TermLiteral _ -> True
    TermFunction f -> functionIsValue f
    TermList els -> forList els
    TermMap map -> L.foldl
      (\b (k, v) -> b && termIsValue g k && termIsValue g v)
      True $ M.toList map
    TermOptional m -> case m of
      Nothing -> True
      Just term -> termIsValue g term
    TermRecord (Record _ fields) -> checkFields fields
    TermSet els -> forList $ S.toList els
    TermUnion (Injection _ field) -> checkField field
    TermVariable _ -> False
  where
    forList els = L.foldl (\b t -> b && termIsValue g t) True els
    checkField = termIsValue g . fieldTerm
    checkFields = L.foldl (\b f -> b && checkField f) True

    functionIsValue f = case f of
      FunctionElimination e -> case e of
        EliminationWrap _ -> True
        EliminationOptional (OptionalCases nothing just) -> termIsValue g nothing
          && termIsValue g just
        EliminationRecord _ -> True
        EliminationUnion (CaseStatement _ def cases) -> checkFields cases && (Y.maybe True (termIsValue g) def)
      FunctionLambda (Lambda _ _ body) -> termIsValue g body
      FunctionPrimitive _ -> True
