-- | Entry point for Hydra type inference, which is a variation on on Hindley-Milner

module Hydra.Inference (
  annotateTermWithTypes,
  inferGraphTypes,
  inferType,
  inferTypeAndConstraints,
  Constraint,
) where

import Hydra.Compute
import Hydra.Core
import Hydra.CoreEncoding
import Hydra.Graph
import Hydra.Lexical
import Hydra.Mantle
import Hydra.Kv
import Hydra.Reduction
import Hydra.Rewriting
import Hydra.Substitution
import Hydra.Unification
import Hydra.Rules
import Hydra.Tier1
import Hydra.Tier2
import Hydra.Tools.Sorting
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


annotateElements :: (Ord a, Show a) => Graph a -> [Element a] -> Flow (Graph a) [Element a]
annotateElements g sortedEls = initializeGraph $ do
    rels <- annotate sortedEls []

    -- Note: inference occurs over the entire graph at once,
    --       but unification and substitution occur within elements in isolation
    let constraints = inferredConstraints . snd <$> rels
    subst <- withSchemaContext $ CM.mapM solveConstraints constraints
    CM.zipWithM rewriteElement subst rels
  where
    rewriteElement subst (name, rel) = do
        anns <- graphAnnotations <$> getState
        term <- substituteAndNormalizeAnnotations anns subst $ inferredTerm rel
        return $ Element name term

    annotate original annotated = case original of
      [] -> pure $ L.reverse annotated
      (el:rest) -> do
        rel <- inferElementType el
        withBinding (fst rel) (inferredType $ snd rel) $ annotate rest (rel:annotated)

annotateTermWithTypes :: (Ord a, Show a) => Term a -> Flow (Graph a) (Term a)
annotateTermWithTypes = inferTypeAndConstraints

inferElementType :: (Ord a, Show a) => Element a -> Flow (Graph a) (Name, Inferred a)
inferElementType el = withTrace ("infer type of " ++ unName (elementName el)) $ do
  rterm <- infer $ elementData el
  return (elementName el, rterm)

inferGraphTypes :: (Ord a, Show a) => Flow (Graph a) (Graph a)
inferGraphTypes = getState >>= annotateGraph
  where
    annotateGraph g = withTrace ("infer graph types") $ do
        sorted <- sortGraphElements g
        els <- sortGraphElements g >>= annotateElements g
        return g {graphElements = M.fromList (toPair <$> els)}
      where
        toPair el = (elementName el, el)

-- TODO: deprecated; inference is performed on graphs, not individual terms. Update the Haskell coder to use inferElementType
inferType :: (Ord a, Show a) => Term a -> Flow (Graph a) (Type a)
--inferType term = (simplifyUniversalTypes . termType) <$> inferTypeAndConstraints term
inferType term = do
  term1 <- inferTypeAndConstraints term
  anns <- graphAnnotations <$> getState
  mtyp <- annotationClassTermType anns term1
  return $ Y.fromJust mtyp

-- TODO: deprecated; inference is performed on graphs, not individual terms. Update tests to use inferElementType
-- | Solve for the top-level type of an expression in a given environment
inferTypeAndConstraints :: (Ord a, Show a) => Term a -> Flow (Graph a) (Term a)
inferTypeAndConstraints term = withTrace ("infer type") $ initializeGraph $ do
    rterm <- infer term
    subst <- withSchemaContext $ solveConstraints (inferredConstraints rterm)
    anns <- graphAnnotations <$> getState
    substituteAndNormalizeAnnotations anns subst $ inferredTerm rterm

initializeGraph flow = do
    g <- getState
    env <- initialEnv g $ graphAnnotations g
    withState (g {graphTypes = env}) flow
  where
    initialEnv g anns = M.fromList . Y.catMaybes <$> (CM.mapM toPair $ M.elems $ graphElements g)
      where
        toPair el = do
          mt <- annotationClassTermType anns $ elementData el
          return $ (\t -> (elementName el, t)) <$> mt

normalizeType :: Ord a => Type a -> Type a
normalizeType = rewriteType f id
  where
    f recurse typ = yank $ recurse typ
      where
        yank typ = case typ of
          TypeAnnotated (Annotated typ1 ann) -> normalize typ1 $ \typ2 -> TypeAnnotated $ Annotated typ2 ann
          TypeApplication (ApplicationType lhs rhs) -> normalize lhs $ \lhs1 ->
            normalize rhs $ \rhs1 -> case lhs of
              TypeLambda (LambdaType var body) -> alphaConvertType var rhs1 body
              _ -> TypeApplication $ ApplicationType lhs1 rhs1
          TypeFunction (FunctionType dom cod) -> normalize dom $
            \dom1 -> normalize cod $
            \cod1 -> TypeFunction $ FunctionType dom1 cod1
          TypeList lt -> normalize lt TypeList
          TypeMap (MapType kt vt) -> normalize kt (\kt1 -> normalize vt (\vt1 -> TypeMap $ MapType kt1 vt1))
          TypeOptional ot -> normalize ot TypeOptional
          TypeProduct types -> case types of
            [] -> TypeProduct []
            (h:rest) -> normalize h
              $ \h1 -> normalize (yank $ TypeProduct rest)
                $ \(TypeProduct rest2) -> TypeProduct $ h1:rest2
          TypeRecord (RowType tname ext fields) -> case fields of
            [] -> TypeRecord (RowType tname ext [])
            ((FieldType fname h):rest) -> normalize h $ \h1 -> normalize (yank $ TypeRecord (RowType tname ext rest))
              $ \(TypeRecord (RowType _ _ rest2)) -> TypeRecord $ RowType tname ext ((FieldType fname h1):rest2)
          TypeSet st -> normalize st TypeSet
          TypeStream st -> normalize st TypeStream
          TypeSum types -> case types of
            [] -> TypeSum []
            (h:rest) -> normalize h $ \h1 -> normalize (yank $ TypeSum rest) $ \(TypeSum rest2) -> TypeSum $ h1:rest2
          TypeUnion (RowType tname ext fields) -> case fields of
            [] -> TypeUnion (RowType tname ext [])
            ((FieldType fname h):rest) -> normalize h $ \h1 -> normalize (yank $ TypeUnion (RowType tname ext rest))
              $ \(TypeUnion (RowType _ _ rest2)) -> TypeUnion $ RowType tname ext ((FieldType fname h1):rest2)
          TypeWrap (Nominal name t) -> normalize t (TypeWrap . Nominal name)
          t -> t
        normalize subtype build = case subtype of
          TypeLambda (LambdaType var body) -> TypeLambda $ LambdaType var $ yank $ build body
          t -> build t

sortGraphElements :: (Ord a, Show a) => Graph a -> Flow (Graph a) [Element a]
sortGraphElements g = do
    annotated <- S.fromList . Y.catMaybes <$> (CM.mapM ifAnnotated $ M.elems els)
    adjList <- CM.mapM (toAdj annotated) $ M.elems els
    case topologicalSort adjList of
      Left comps -> fail $ "cyclical dependency not resolved through annotations: " ++ L.intercalate ", " (unName <$> L.head comps)
      Right names -> return $ Y.catMaybes ((\n -> M.lookup n els) <$> names)
  where
    els = graphElements g
    ifAnnotated el = do
      mtyp <- annotationClassTermType (graphAnnotations g) $ elementData el
      return $ case mtyp of
        Nothing -> Nothing
        Just _ -> Just $ elementName el
    toAdj annotated el = do
        let deps = L.filter isNotAnnotated $ L.filter isElName $ S.toList $ freeVariablesInTerm $ elementData el

        return (elementName el, deps)
      where
        -- Ignore free variables which are not valid element references
        isElName name = M.member name els
        -- No need for an inference dependency on an element which is already annotated with a type
        isNotAnnotated name = not $ S.member name annotated

substituteAndNormalizeAnnotations :: Ord a => AnnotationClass a -> Subst a -> Term a -> Flow (Graph a) (Term a)
substituteAndNormalizeAnnotations anns subst = rewriteTermMetaM rewrite
  where
    -- Note: normalizing each annotation separately results in different variable names for corresponding types
--    rewrite (x, typ, c) = (x, normalizeTypeVariables $ normalizeType $ substituteTypeVariables subst typ, c) -- TODO: restore this
    rewrite ann = do
      mtyp <- annotationClassTypeOf anns ann
      let ntyp = (normalizeType . substituteTypeVariables subst) <$> mtyp
      return $ annotationClassSetTypeOf anns ntyp ann
--    rewrite (x, typ, c) = (x, normalizeType $ substituteTypeVariables subst typ, c)
--    rewrite (x, typ, c) = (x, normalizeType $ substituteTypeVariables subst typ, c)
