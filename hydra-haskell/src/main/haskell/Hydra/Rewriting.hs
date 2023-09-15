-- | Functions for type and term rewriting

module Hydra.Rewriting where

import Hydra.Basics
import Hydra.Strip
import Hydra.Coders
import Hydra.Compute
import Hydra.Core
import Hydra.CoreEncoding
import Hydra.Extras
import Hydra.Graph
import Hydra.Module
import Hydra.Lexical
import Hydra.Mantle
import Hydra.Tools.Sorting
import Hydra.Tier1
import Hydra.Tier2
import Hydra.Tools.Debug

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


boundVariablesInType :: Type -> S.Set Name
boundVariablesInType = foldOverType TraversalOrderPre fld S.empty
  where
    fld names typ = case typ of
      TypeLambda (LambdaType v _) -> S.insert v names
      _ -> names

elementsWithDependencies :: [Element Kv] -> Flow (Graph Kv) [Element Kv]
elementsWithDependencies original = CM.mapM requireElement allDepNames
  where
    depNames = S.toList . termDependencyNames True False False . elementData
    allDepNames = L.nub $ (elementName <$> original) ++ (L.concat $ depNames <$> original)

-- | Turn arbitrary terms like 'add 42' into terms like '\x.add 42 x',
--   whose arity (in the absence of application terms) is equal to the depth of nested lambdas.
--   This function leaves application terms intact, simply rewriting their left and right subterms.
expandLambdas :: Term -> Flow (Graph Kv) (Term)
expandLambdas term = do
    g <- getState
    rewriteTermM (expand g Nothing []) (pure . id) term
  where
    expand g mtyp args recurse term = case term of
        TermAnnotated (Annotated term' ann) -> do
          mt <- annotationClassTermType (graphAnnotations g) term
          expanded <- expand g (Y.maybe mtyp Just mt) args recurse term'
          return $ TermAnnotated $ Annotated expanded ann
        TermApplication (Application lhs rhs) -> do
          rhs' <- expandLambdas rhs
          expand g Nothing (rhs':args) recurse lhs
        TermFunction f -> case f of
          FunctionElimination _ -> pad g mtyp args 1 <$> recurse term
          FunctionPrimitive name -> do
            prim <- requirePrimitive name
            return $ pad g mtyp args (primitiveArity prim) term
          _ -> passThrough
        _ -> passThrough
      where
        passThrough = pad g mtyp args 0 <$> recurse term

    pad g mtyp args arity term = L.foldl lam (app mtyp term args') $ L.reverse variables
      where
        variables = L.take (max 0 (arity - L.length args)) ((\i -> Name $ "v" ++ show i) <$> [1..])
        args' = args ++ (TermVariable <$> variables)

        lam body v = TermFunction $ FunctionLambda $ Lambda v body

        app mtyp lhs args = case args of
          [] -> lhs
          (a:rest) -> app mtyp' (TermApplication $ Application lhs' a) rest
            where
              lhs' = annotationClassSetTermType (graphAnnotations g) mtyp lhs
              mtyp' = case mtyp of
                Just t -> case stripTypeParameters $ stripType t of
                  TypeFunction (FunctionType _ cod) -> Just cod
                  _ -> throwDebugException $ "expandLambdas: expected function type, got " ++ show t
                Nothing -> Nothing

freeVariablesInScheme :: TypeScheme Kv -> S.Set Name
freeVariablesInScheme (TypeScheme vars t) = S.difference (freeVariablesInType t) (S.fromList vars)

isFreeIn :: Name -> Term -> Bool
isFreeIn v term = not $ S.member v $ freeVariablesInTerm term

-- | Recursively remove term annotations, including within subterms
removeTermAnnotations :: Term -> Term
removeTermAnnotations = rewriteTerm remove id
  where
    remove recurse term = case term of
      TermAnnotated (Annotated term' _) -> remove recurse term'
      _ -> recurse term

-- | Recursively remove type annotations, including within subtypes
removeTypeAnnotations :: Type -> Type
removeTypeAnnotations = rewriteType remove id
  where
    remove recurse typ = case recurse typ of
      TypeAnnotated (Annotated typ' _) -> remove recurse typ'
      _ -> recurse typ

replaceFreeName :: Name -> Type -> Type -> Type
replaceFreeName v rep = rewriteType mapExpr id
  where
    mapExpr recurse t = case t of
      TypeLambda (LambdaType v' body) -> if v == v'
        then t
        else TypeLambda $ LambdaType v' $ recurse body
      TypeVariable v' -> if v == v' then rep else t
      _ -> recurse t

rewrite :: ((x -> y) -> x -> y) -> ((x -> y) -> x -> y) -> x -> y
rewrite fsub f = recurse
  where
    recurse = f (fsub recurse)

rewriteTerm :: ((Term -> Term) -> Term -> Term) -> (Kv -> Kv) -> Term -> Term
rewriteTerm f mf = rewrite fsub f
  where
    fsub recurse term = case term of
        TermAnnotated (Annotated ex ann) -> TermAnnotated $ Annotated (recurse ex) (mf ann)
        TermApplication (Application lhs rhs) -> TermApplication $ Application (recurse lhs) (recurse rhs)
        TermFunction fun -> TermFunction $ case fun of
          FunctionElimination e -> FunctionElimination $ case e of
            EliminationList fld -> EliminationList $ recurse fld
            EliminationOptional (OptionalCases nothing just) -> EliminationOptional
              (OptionalCases (recurse nothing) (recurse just))
            EliminationProduct tp -> EliminationProduct tp
            EliminationRecord p -> EliminationRecord p
            EliminationUnion (CaseStatement n def cases) -> EliminationUnion $ CaseStatement n (recurse <$> def) (forField <$> cases)
            EliminationWrap name -> EliminationWrap name
          FunctionLambda (Lambda v body) -> FunctionLambda $ Lambda v $ recurse body
          FunctionPrimitive name -> FunctionPrimitive name
        TermLet (Let bindings env) -> TermLet $ Let (M.fromList (mapBinding <$> M.toList bindings)) (recurse env)
          where
            mapBinding (k, t) = (k, recurse t)
        TermList els -> TermList $ recurse <$> els
        TermLiteral v -> TermLiteral v
        TermMap m -> TermMap $ M.fromList $ (\(k, v) -> (recurse k, recurse v)) <$> M.toList m
        TermWrap (Nominal name t) -> TermWrap (Nominal name $ recurse t)
        TermOptional m -> TermOptional $ recurse <$> m
        TermProduct tuple -> TermProduct (recurse <$> tuple)
        TermRecord (Record n fields) -> TermRecord $ Record n $ forField <$> fields
        TermSet s -> TermSet $ S.fromList $ recurse <$> S.toList s
        TermSum (Sum i s trm) -> TermSum $ Sum i s $ recurse trm
        TermUnion (Injection n field) -> TermUnion $ Injection n $ forField field
        TermVariable v -> TermVariable v
      where
        forField f = f {fieldTerm = recurse (fieldTerm f)}

rewriteTermM ::
  ((Term -> Flow s (Term)) -> Term -> (Flow s (Term))) ->
  (Kv -> Flow s Kv) ->
  Term ->
  Flow s (Term)
rewriteTermM f mf = rewrite fsub f
  where
    fsub recurse term = case term of
        TermAnnotated (Annotated ex ma) -> TermAnnotated <$> (Annotated <$> recurse ex <*> mf ma)
        TermApplication (Application lhs rhs) -> TermApplication <$> (Application <$> recurse lhs <*> recurse rhs)
        TermFunction fun -> TermFunction <$> case fun of
          FunctionElimination e -> FunctionElimination <$> case e of
            EliminationList fld -> EliminationList <$> recurse fld
            EliminationOptional (OptionalCases nothing just) -> EliminationOptional <$>
              (OptionalCases <$> recurse nothing <*> recurse just)
            EliminationProduct tp -> pure $ EliminationProduct tp
            EliminationRecord p -> pure $ EliminationRecord p
            EliminationUnion (CaseStatement n def cases) -> do
              rdef <- case def of
                Nothing -> pure Nothing
                Just t -> Just <$> recurse t
              EliminationUnion <$> (CaseStatement n rdef <$> (CM.mapM forField cases))
            EliminationWrap name -> pure $ EliminationWrap name
          FunctionLambda (Lambda v body) -> FunctionLambda <$> (Lambda v <$> recurse body)
          FunctionPrimitive name -> pure $ FunctionPrimitive name
        TermLet (Let bindings env) -> TermLet <$> (Let <$> (M.fromList <$> (CM.mapM mapBinding $ M.toList bindings)) <*> recurse env)
          where
            mapBinding (k, t) = do
              t' <- recurse t
              return (k, t')
        TermList els -> TermList <$> (CM.mapM recurse els)
        TermLiteral v -> pure $ TermLiteral v
        TermMap m -> TermMap <$> (M.fromList <$> CM.mapM forPair (M.toList m))
          where
            forPair (k, v) = do
              km <- recurse k
              vm <- recurse v
              return (km, vm)
        TermOptional m -> TermOptional <$> (CM.mapM recurse m)
        TermProduct tuple -> TermProduct <$> (CM.mapM recurse tuple)
        TermRecord (Record n fields) -> TermRecord <$> (Record n <$> (CM.mapM forField fields))
        TermSet s -> TermSet <$> (S.fromList <$> (CM.mapM recurse $ S.toList s))
        TermSum (Sum i s trm) -> TermSum <$> (Sum i s <$> recurse trm)
        TermUnion (Injection n field) -> TermUnion <$> (Injection n <$> forField field)
        TermVariable v -> pure $ TermVariable v
        TermWrap (Nominal name t) -> TermWrap <$> (Nominal name <$> recurse t)
      where
        forField f = do
          t <- recurse (fieldTerm f)
          return f {fieldTerm = t}

rewriteTermMeta :: (Kv -> Kv) -> Term -> Term
rewriteTermMeta = rewriteTerm mapExpr
  where
    mapExpr recurse term = recurse term

rewriteTermMetaM :: (Kv -> Flow s Kv) -> Term -> Flow s (Term)
rewriteTermMetaM = rewriteTermM mapExpr
  where
    mapExpr recurse term = recurse term

rewriteType :: ((Type -> Type) -> Type -> Type) -> (Kv -> Kv) -> Type -> Type
rewriteType f mf = rewrite fsub f
  where
    fsub recurse typ = case typ of
        TypeAnnotated (Annotated t ann) -> TypeAnnotated $ Annotated (recurse t) (mf ann)
        TypeApplication (ApplicationType lhs rhs) -> TypeApplication $ ApplicationType (recurse lhs) (recurse rhs)
        TypeFunction (FunctionType dom cod) -> TypeFunction (FunctionType (recurse dom) (recurse cod))
        TypeLambda (LambdaType v b) -> TypeLambda (LambdaType v $ recurse b)
        TypeList t -> TypeList $ recurse t
        TypeLiteral lt -> TypeLiteral lt
        TypeMap (MapType kt vt) -> TypeMap (MapType (recurse kt) (recurse vt))
        TypeOptional t -> TypeOptional $ recurse t
        TypeProduct types -> TypeProduct (recurse <$> types)
        TypeRecord (RowType name extends fields) -> TypeRecord $ RowType name extends (forField <$> fields)
        TypeSet t -> TypeSet $ recurse t
        TypeSum types -> TypeSum (recurse <$> types)
        TypeUnion (RowType name extends fields) -> TypeUnion $ RowType name extends (forField <$> fields)
        TypeVariable v -> TypeVariable v
        TypeWrap (Nominal name t) -> TypeWrap $ Nominal name $ recurse t
      where
        forField f = f {fieldTypeType = recurse (fieldTypeType f)}

rewriteTypeM ::
  ((Type -> Flow s (Type)) -> Type -> (Flow s (Type))) ->
  (Kv -> Flow s Kv) ->
  Type ->
  Flow s (Type)
rewriteTypeM f mf = rewrite fsub f
  where
    fsub recurse typ = case typ of
        TypeAnnotated (Annotated t ann) -> TypeAnnotated <$> (Annotated <$> recurse t <*> mf ann)
        TypeApplication (ApplicationType lhs rhs) -> TypeApplication <$> (ApplicationType <$> recurse lhs <*> recurse rhs)
        TypeFunction (FunctionType dom cod) -> TypeFunction <$> (FunctionType <$> recurse dom <*> recurse cod)
        TypeLambda (LambdaType v b) -> TypeLambda <$> (LambdaType <$> pure v <*> recurse b)
        TypeList t -> TypeList <$> recurse t
        TypeLiteral lt -> pure $ TypeLiteral lt
        TypeMap (MapType kt vt) -> TypeMap <$> (MapType <$> recurse kt <*> recurse vt)
        TypeOptional t -> TypeOptional <$> recurse t
        TypeProduct types -> TypeProduct <$> CM.mapM recurse types
        TypeRecord (RowType name extends fields) ->
          TypeRecord <$> (RowType <$> pure name <*> pure extends <*> CM.mapM forField fields)
        TypeSet t -> TypeSet <$> recurse t
        TypeSum types -> TypeSum <$> CM.mapM recurse types
        TypeUnion (RowType name extends fields) ->
          TypeUnion <$> (RowType <$> pure name <*> pure extends <*> CM.mapM forField fields)
        TypeVariable v -> pure $ TypeVariable v
        TypeWrap (Nominal name t) -> TypeWrap <$> (Nominal <$> pure name <*> recurse t)
      where
        forField f = do
          t <- recurse $ fieldTypeType f
          return f {fieldTypeType = t}

rewriteTypeMeta :: (Kv -> Kv) -> Type -> Type
rewriteTypeMeta = rewriteType mapExpr
  where
    mapExpr recurse term = recurse term

simplifyTerm :: Term -> Term
simplifyTerm = rewriteTerm simplify id
  where
    simplify recurse term = recurse $ case stripTerm term of
      TermApplication (Application lhs rhs) -> case stripTerm lhs of
        TermFunction (FunctionLambda (Lambda var body)) ->
          if S.member var (freeVariablesInTerm body)
            then case stripTerm rhs of
              TermVariable v -> simplifyTerm $ substituteVariable var v body
              _ -> term
            else simplifyTerm body
        _ -> term
      _ -> term

simplifyUniversalTypes :: Type -> Type
simplifyUniversalTypes = rewriteType f id
  where
    f recurse t = case recurse t of
      -- Caution: time complexity
      TypeLambda (LambdaType v body) -> if S.member v (freeVariablesInType body)
        then t
        else body
      _ -> t

substituteVariable :: Name -> Name -> Term -> Term
substituteVariable from to = rewriteTerm replace id
  where
    replace recurse term = case term of
      TermVariable x -> recurse $ (TermVariable $ if x == from then to else x)
      TermFunction (FunctionLambda (Lambda var _)) -> if var == from
        then term
        else recurse term
      _ -> recurse term

-- Note: does not distinguish between bound and free variables; use freeVariablesInTerm for that
termDependencyNames :: Bool -> Bool -> Bool -> Term -> S.Set Name
termDependencyNames withVars withPrims withNoms = foldOverTerm TraversalOrderPre addNames S.empty
  where
    addNames names term = case term of
        TermFunction f -> case f of
          FunctionPrimitive name -> prim name
          FunctionElimination e -> case e of
            EliminationRecord (Projection name _) -> nominal name
            EliminationUnion (CaseStatement name _ _) -> nominal name
            EliminationWrap name -> nominal name
            _ -> names
          _ -> names
        TermRecord (Record name _) -> nominal name
        TermUnion (Injection name _) -> nominal name
        TermVariable name -> var name
        TermWrap (Nominal name _) -> nominal name
        _ -> names
      where
        nominal name = if withNoms then S.insert name names else names
        prim name = if withPrims then S.insert name names else names
        var name = if withVars then S.insert name names else names

topologicalSortElements :: [Element Kv] -> Either [[Name]] [Name]
topologicalSortElements els = topologicalSort $ adjlist <$> els
  where
    adjlist e = (elementName e, S.toList $ termDependencyNames False True True $ elementData e)

typeDependencyNames :: Type -> S.Set Name
typeDependencyNames = freeVariablesInType

-- | Where non-lambda terms with nonzero arity occur at the top level, turn them into lambdas,
--   also adding an appropriate type annotation to each new lambda.
wrapLambdas :: Term -> Flow (Graph Kv) (Term)
wrapLambdas term = do
    typ <- requireTermType term
    anns <- graphAnnotations <$> getState
    let types = uncurryType typ
    let argTypes = L.init types
    let missing = missingArity (L.length argTypes) term
    return $ pad anns term (L.take missing argTypes) (toFunType $ L.drop missing types)
  where
    toFunType types = case types of
      [t] -> t
      (dom:rest) -> TypeFunction $ FunctionType dom $ toFunType rest
    missingArity arity term = if arity == 0
      then 0
      else case term of
        TermAnnotated (Annotated term2 _) -> missingArity arity term2
        TermLet (Let _ env) -> missingArity arity env
        TermFunction (FunctionLambda (Lambda _ body)) -> missingArity (arity - 1) body
        _ -> arity
    pad anns term doms cod = fst $ L.foldl newLambda (apps, cod) $ L.reverse variables
      where
        newLambda (body, cod) (v, dom) = (annotationClassSetTermType anns (Just ft) $ TermFunction $ FunctionLambda $ Lambda v body, ft)
          where
            ft = TypeFunction $ FunctionType dom cod
        apps = L.foldl (\lhs (v, _) -> TermApplication (Application lhs $ TermVariable v)) term variables
        variables = L.zip ((\i -> Name $ "a" ++ show i) <$> [1..]) doms
