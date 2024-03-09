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
import Hydra.Annotations
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


alphaConvertTerm :: Name -> Term -> Term -> Term
alphaConvertTerm vold tnew = rewriteTerm rewrite
  where
    rewrite recurse term = case term of
      TermFunction (FunctionLambda (Lambda v _ _)) -> if v == vold
        then term
        else recurse term
      TermVariable v -> if v == vold then tnew else TermVariable v
      _ -> recurse term

alphaConvertType :: Name -> Type -> Type -> Type
alphaConvertType vold tnew = rewriteType rewrite
  where
    rewrite recurse typ = case typ of
      TypeLambda (LambdaType v body) -> if v == vold
        then typ
        else recurse typ
      TypeVariable v -> if v == vold then tnew else TypeVariable v
      _ -> recurse typ

-- | Find all of the bound variables in the type annotations within a System F term.
--   This function considers the types in "typed terms" (term:type), domain types on lambdas (\v:type.term),
--   and also type abstractions (/\v.term) to provide bound type variables.
boundTypeVariablesInSystemFTerm :: Term -> [Name]
boundTypeVariablesInSystemFTerm = L.nub . foldOverTerm TraversalOrderPost addTypeVars []
  where
    addTypeVars vars term = typeVarsIn term ++ vars
    typeVarsIn term = case term of
      TermFunction (FunctionLambda (Lambda _ (Just typ) _)) -> boundVariablesInTypeOrdered typ
      TermTypeAbstraction (TypeAbstraction v _) -> [v]
      TermTyped (TypedTerm typ term) -> boundVariablesInTypeOrdered typ
      _ -> []

boundTypeVariablesInTermOrdered :: Term -> [Name]
boundTypeVariablesInTermOrdered = L.nub . foldOverTerm TraversalOrderPre fld []
  where
    fld vars term = case term of
      TermTyped (TypedTerm typ _) -> variablesInTypeOrdered False typ ++ vars
      _ -> vars

-- | Finds all of the universal type variables in a type expression, in the order in which they appear.
-- Note: this function assumes that there are no shadowed type variables, as in (forall a. forall a. a)
-- TODO: redundant with variablesInTypeOrdered
boundVariablesInTypeOrdered :: Type -> [Name]
boundVariablesInTypeOrdered typ = case typ of
  TypeLambda (LambdaType var body) -> var:(boundVariablesInTypeOrdered body)
  t -> L.concat (boundVariablesInTypeOrdered <$> subtypes t)

elementsWithDependencies :: [Element] -> Flow Graph [Element]
elementsWithDependencies original = CM.mapM requireElement allDepNames
  where
    depNames = S.toList . termDependencyNames True False False . elementData
    allDepNames = L.nub $ (elementName <$> original) ++ (L.concat $ depNames <$> original)

-- | Turn arbitrary terms like 'add 42' into terms like '\x.add 42 x',
--   whose arity (in the absence of application terms) is equal to the depth of nested lambdas.
--   This function leaves application terms intact, simply rewriting their left and right subterms.
--   Note that domain types are currently dropped from lambdas in this process.
expandLambdas :: Term -> Flow Graph Term
expandLambdas term = do
    g <- getState
    rewriteTermM (expand g Nothing []) term
  where
    expand g mtyp args recurse term = case term of
        TermAnnotated (Annotated term' ann) -> do
          let mt = getTermType term
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

        lam body v = TermFunction $ FunctionLambda $ Lambda v Nothing body

        app mtyp lhs args = case args of
          [] -> lhs
          (a:rest) -> app mtyp' (TermApplication $ Application lhs' a) rest
            where
              lhs' = setTermType mtyp lhs
              mtyp' = case mtyp of
                Just t -> case stripTypeParameters $ stripType t of
                  TypeFunction (FunctionType _ cod) -> Just cod
                  _ -> throwDebugException $ "expandLambdas: expected function type, got " ++ show t
                Nothing -> Nothing

foldOverTermM :: TraversalOrder -> (a -> Term -> Flow s a) -> a -> Term -> Flow s a
foldOverTermM order fld b0 term = ((\x -> case x of
  TraversalOrderPre -> do
    term1 <- fld b0 term
    CM.foldM (foldOverTermM order fld) term1 (subterms term)
  TraversalOrderPost -> do
    res <- CM.foldM (foldOverTermM order fld) b0 (subterms term)
    fld res term)) order

freeVariablesInScheme :: TypeScheme -> S.Set Name
freeVariablesInScheme (TypeScheme vars t) = S.difference (freeVariablesInType t) (S.fromList vars)

-- | Find the free variables (i.e. variables not bound by a lambda) in a type,
--   in a well-defined order following a preorder traversal of the type expression.
freeVariablesInTypeOrdered :: Type -> [Name]
freeVariablesInTypeOrdered typ = case typ of
  TypeLambda v -> L.delete (lambdaTypeParameter v) $ freeVariablesInTypeOrdered (lambdaTypeBody v)
  TypeVariable v -> [v]
  -- Note: repeated 'nub'
  _ -> L.nub $ L.concat (freeVariablesInTypeOrdered <$> subtypes typ)

isFreeIn :: Name -> Term -> Bool
isFreeIn v term = not $ S.member v $ freeVariablesInTerm term

-- | Implements specific rules which lift "forall" types out of subtype expressions
--   E.g. [\a.a] becomes \a.[a]
normalizePolytypes :: Type -> Type
normalizePolytypes = rewriteType (\recurse -> lift . recurse)
  where
    lift typ = case typ of
      TypeApplication (ApplicationType lhs rhs) -> liftTwo lhs rhs $ \l r -> TypeApplication $ ApplicationType l r
      TypeFunction (FunctionType dom cod) -> liftTwo dom cod $ \d c -> TypeFunction $ FunctionType d c
      TypeList lt -> liftOne lt TypeList
      TypeMap (MapType kt vt) -> liftTwo kt vt $ \k v -> TypeMap $ MapType k v
      TypeOptional ot -> liftOne ot TypeOptional
      TypeProduct types -> liftMany types TypeProduct
      TypeRecord rt -> liftRowType rt TypeRecord
      TypeSet st -> liftOne st TypeSet
      TypeStream st -> liftOne st TypeStream
      TypeSum types -> liftMany types TypeSum
      TypeUnion rt -> liftRowType rt TypeUnion
      TypeWrap (Nominal name t) -> liftOne t (TypeWrap . Nominal name)
      t -> t
    liftOne subtype build = case subtype of
      TypeAnnotated (Annotated t ann) -> liftOne t $ \t2 -> build $ TypeAnnotated $ Annotated t2 ann
      TypeLambda (LambdaType var body) -> TypeLambda $ LambdaType var $ liftOne body build
      _ -> build subtype
    liftTwo left right build = liftOne left $
      \n1 -> liftOne right $ \n2 -> build n1 n2
    liftMany subtypes build = case subtypes of
      [] -> build []
      (h:rest) -> liftOne h $ \h1 -> liftMany rest $ \rest1 -> build $ h1:rest1
    liftRowType (RowType name extends fields) build = liftMany types $
        \ts -> build $ RowType name extends (L.zipWith FieldType names ts)
      where
        names = fieldTypeName <$> fields
        types = fieldTypeType <$> fields

-- | Recursively remove term annotations, including within subterms
removeTermAnnotations :: Term -> Term
removeTermAnnotations = rewriteTerm remove
  where
    remove recurse term = case term of
      TermAnnotated (Annotated term' _) -> remove recurse term'
      _ -> recurse term

-- | Recursively remove type annotations, including within subtypes
removeTypeAnnotations :: Type -> Type
removeTypeAnnotations = rewriteType remove
  where
    remove recurse typ = case recurse typ of
      TypeAnnotated (Annotated typ' _) -> remove recurse typ'
      _ -> recurse typ

replaceFreeName :: Name -> Type -> Type -> Type
replaceFreeName v rep = rewriteType mapExpr
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

rewriteTerm :: ((Term -> Term) -> Term -> Term) -> Term -> Term
rewriteTerm = rewrite $ \recurse term -> case term of
    TermAnnotated (Annotated ex ann) -> TermAnnotated $ Annotated (recurse ex) ann
    TermApplication (Application lhs rhs) -> TermApplication $ Application (recurse lhs) (recurse rhs)
    TermFunction fun -> TermFunction $ case fun of
      FunctionElimination e -> FunctionElimination $ case e of
        EliminationList fld -> EliminationList $ recurse fld
        EliminationOptional (OptionalCases nothing just) -> EliminationOptional
          (OptionalCases (recurse nothing) (recurse just))
        EliminationProduct tp -> EliminationProduct tp
        EliminationRecord p -> EliminationRecord p
        EliminationUnion (CaseStatement n def cases) -> EliminationUnion $ CaseStatement n (recurse <$> def) (forField recurse <$> cases)
        EliminationWrap name -> EliminationWrap name
      FunctionLambda (Lambda v dom body) -> FunctionLambda $ Lambda v dom $ recurse body
      FunctionPrimitive name -> FunctionPrimitive name
    TermLet (Let bindings env) -> TermLet $ Let (mapBinding <$> bindings) (recurse env)
      where
        mapBinding (Field k t) = Field k $ recurse t
    TermList els -> TermList $ recurse <$> els
    TermLiteral v -> TermLiteral v
    TermMap m -> TermMap $ M.fromList $ (\(k, v) -> (recurse k, recurse v)) <$> M.toList m
    TermWrap (Nominal name t) -> TermWrap (Nominal name $ recurse t)
    TermOptional m -> TermOptional $ recurse <$> m
    TermProduct tuple -> TermProduct (recurse <$> tuple)
    TermRecord (Record n fields) -> TermRecord $ Record n $ forField recurse <$> fields
    TermSet s -> TermSet $ S.fromList $ recurse <$> S.toList s
    TermSum (Sum i s trm) -> TermSum $ Sum i s $ recurse trm
    TermTypeAbstraction (TypeAbstraction v body) -> TermTypeAbstraction $ TypeAbstraction v $ recurse body
    TermTypeApplication (TypedTerm typ trm) -> TermTypeApplication $ TypedTerm typ $ recurse term
    TermTyped (TypedTerm typ trm) -> TermTyped $ TypedTerm typ $ recurse trm
    TermUnion (Injection n field) -> TermUnion $ Injection n $ forField recurse field
    TermVariable v -> TermVariable v
  where
    forField recurse f = f {fieldTerm = recurse (fieldTerm f)}

rewriteTermM :: ((Term -> Flow s Term) -> Term -> (Flow s Term)) -> Term -> Flow s Term
rewriteTermM = rewrite $ \recurse term -> case term of
    TermAnnotated (Annotated ex ma) -> TermAnnotated <$> (Annotated <$> recurse ex <*> pure ma)
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
          EliminationUnion <$> (CaseStatement n rdef <$> (CM.mapM (forField recurse) cases))
        EliminationWrap name -> pure $ EliminationWrap name
      FunctionLambda (Lambda v dom body) -> FunctionLambda <$> (Lambda v dom <$> recurse body)
      FunctionPrimitive name -> pure $ FunctionPrimitive name
    TermLet (Let bindings env) -> TermLet <$> (Let <$> (CM.mapM mapBinding bindings) <*> recurse env)
      where
        mapBinding (Field k t) = do
          t' <- recurse t
          return $ Field k t'
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
    TermRecord (Record n fields) -> TermRecord <$> (Record n <$> (CM.mapM (forField recurse) fields))
    TermSet s -> TermSet <$> (S.fromList <$> (CM.mapM recurse $ S.toList s))
    TermSum (Sum i s trm) -> TermSum <$> (Sum i s <$> recurse trm)
    TermTypeAbstraction (TypeAbstraction v body) -> TermTypeAbstraction <$> (TypeAbstraction v <$> recurse body)
    TermTypeApplication (TypedTerm typ trm) -> TermTypeApplication <$> (TypedTerm typ <$> recurse trm)
    TermTyped (TypedTerm typ trm) -> TermTyped <$> (TypedTerm typ <$> recurse trm)
    TermUnion (Injection n field) -> TermUnion <$> (Injection n <$> forField recurse field)
    TermVariable v -> pure $ TermVariable v
    TermWrap (Nominal name t) -> TermWrap <$> (Nominal name <$> recurse t)
  where
    forField recurse f = do
      t <- recurse (fieldTerm f)
      return f {fieldTerm = t}

rewriteTermAnnotations :: (M.Map String Term -> M.Map String Term) -> Term -> Term
rewriteTermAnnotations f = rewriteTerm mapExpr
  where
    mapExpr recurse term = case term of
      TermAnnotated (Annotated term1 ann) -> TermAnnotated $ Annotated (recurse term1) (f ann)
      _ -> recurse term

rewriteTermAnnotationsM :: (M.Map String Term -> Flow s (M.Map String Term)) -> Term -> Flow s Term
rewriteTermAnnotationsM f = rewriteTermM mapExpr
  where
    mapExpr recurse term = do
      rec <- recurse term
      case rec of
        TermAnnotated (Annotated subj ann) -> TermAnnotated <$> (Annotated <$> pure subj <*> f ann)
        _ -> pure rec

rewriteTermTypes :: (Type -> Type) -> Term -> Term
rewriteTermTypes f = rewriteTerm mapExpr
  where
    mapExpr recurse term = case recurse term of
      TermTyped (TypedTerm typ t) -> TermTyped $ TypedTerm (f typ) t
      TermFunction (FunctionLambda (Lambda var (Just typ) body)) -> TermFunction $ FunctionLambda $
        Lambda var (Just $ f typ) body
      -- TODO: support for type abstraction?
      TermTypeApplication (TypedTerm typ t) -> TermTypeApplication $ TypedTerm (f typ) t
      t -> t

rewriteType :: ((Type -> Type) -> Type -> Type) -> Type -> Type
rewriteType = rewrite $ \recurse typ -> case typ of
    TypeAnnotated (Annotated t ann) -> TypeAnnotated $ Annotated (recurse t) ann
    TypeApplication (ApplicationType lhs rhs) -> TypeApplication $ ApplicationType (recurse lhs) (recurse rhs)
    TypeFunction (FunctionType dom cod) -> TypeFunction (FunctionType (recurse dom) (recurse cod))
    TypeLambda (LambdaType v b) -> TypeLambda (LambdaType v $ recurse b)
    TypeList t -> TypeList $ recurse t
    TypeLiteral lt -> TypeLiteral lt
    TypeMap (MapType kt vt) -> TypeMap (MapType (recurse kt) (recurse vt))
    TypeOptional t -> TypeOptional $ recurse t
    TypeProduct types -> TypeProduct (recurse <$> types)
    TypeRecord (RowType name extends fields) -> TypeRecord $ RowType name extends (forField recurse <$> fields)
    TypeSet t -> TypeSet $ recurse t
    TypeStream t -> TypeStream $ recurse t
    TypeSum types -> TypeSum (recurse <$> types)
    TypeUnion (RowType name extends fields) -> TypeUnion $ RowType name extends (forField recurse <$> fields)
    TypeVariable v -> TypeVariable v
    TypeWrap (Nominal name t) -> TypeWrap $ Nominal name $ recurse t
  where
    forField recurse f = f {fieldTypeType = recurse (fieldTypeType f)}

rewriteTypeM :: ((Type -> Flow s Type) -> Type -> (Flow s Type)) -> Type -> Flow s Type
rewriteTypeM = rewrite $ \recurse typ -> case typ of
    TypeAnnotated (Annotated t ann) -> TypeAnnotated <$> (Annotated <$> recurse t <*> pure ann)
    TypeApplication (ApplicationType lhs rhs) -> TypeApplication <$> (ApplicationType <$> recurse lhs <*> recurse rhs)
    TypeFunction (FunctionType dom cod) -> TypeFunction <$> (FunctionType <$> recurse dom <*> recurse cod)
    TypeLambda (LambdaType v b) -> TypeLambda <$> (LambdaType <$> pure v <*> recurse b)
    TypeList t -> TypeList <$> recurse t
    TypeLiteral lt -> pure $ TypeLiteral lt
    TypeMap (MapType kt vt) -> TypeMap <$> (MapType <$> recurse kt <*> recurse vt)
    TypeOptional t -> TypeOptional <$> recurse t
    TypeProduct types -> TypeProduct <$> CM.mapM recurse types
    TypeRecord (RowType name extends fields) ->
      TypeRecord <$> (RowType <$> pure name <*> pure extends <*> CM.mapM (forField recurse) fields)
    TypeSet t -> TypeSet <$> recurse t
    TypeStream t -> TypeStream <$> recurse t
    TypeSum types -> TypeSum <$> CM.mapM recurse types
    TypeUnion (RowType name extends fields) ->
      TypeUnion <$> (RowType <$> pure name <*> pure extends <*> CM.mapM (forField recurse) fields)
    TypeVariable v -> pure $ TypeVariable v
    TypeWrap (Nominal name t) -> TypeWrap <$> (Nominal <$> pure name <*> recurse t)
  where
    forField recurse f = do
      t <- recurse $ fieldTypeType f
      return f {fieldTypeType = t}

rewriteTypeAnnotations :: (M.Map String Term -> M.Map String Term) -> Type -> Type
rewriteTypeAnnotations f = rewriteType mapExpr
  where
    mapExpr recurse typ = case typ of
      TypeAnnotated (Annotated typ1 ann) -> TypeAnnotated (Annotated (recurse typ1) (f ann))
      _ -> recurse typ

simplifyTerm :: Term -> Term
simplifyTerm = rewriteTerm simplify
  where
    simplify recurse term = recurse $ case stripTerm term of
      TermApplication (Application lhs rhs) -> case stripTerm lhs of
        TermFunction (FunctionLambda (Lambda var _ body)) ->
          if S.member var (freeVariablesInTerm body)
            then case stripTerm rhs of
              TermVariable v -> simplifyTerm $ substituteVariable var v body
              _ -> term
            else simplifyTerm body
        _ -> term
      _ -> term

-- NOTE: currently unused
-- | Pulls all universal type variables to the top of a type expression (but beneath any annotations).
--   Bound type variables which would not otherwise appear free in the body of the type are omitted.
simplifyUniversalTypes :: Type -> Type
simplifyUniversalTypes typ = bury addUniversals stripped
  where
    boundVars = boundVariablesInTypeOrdered typ
    bury f t = case t of
      TypeAnnotated (Annotated t1 ann) -> TypeAnnotated $ Annotated (f t1) ann
      _ -> f t
    addUniversals t = L.foldl (\t v -> TypeLambda (LambdaType v t)) t $ L.reverse minimalBoundVars
    stripUniversals = rewriteType $ \recurse t -> case recurse t of
      TypeLambda (LambdaType _ body) -> body
      t -> t
    stripped = stripUniversals typ
    freeVars = freeVariablesInType stripped
    minimalBoundVars = L.filter (`S.member` freeVars) boundVars

stripUniversalTypes :: Type -> Type
stripUniversalTypes = rewriteType $ \recurse typ -> case recurse typ of
  TypeLambda (LambdaType v body) -> body
  t -> t

substituteVariable :: Name -> Name -> Term -> Term
substituteVariable from to = rewriteTerm replace
  where
    replace recurse term = case term of
      TermVariable x -> recurse $ (TermVariable $ if x == from then to else x)
      TermFunction (FunctionLambda (Lambda var _ _)) -> if var == from
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

-- Topological sort of connected components, in terms of dependencies between varable/term binding pairs
topologicalSortBindings :: [Field] -> [[(Name, Term)]]
topologicalSortBindings bindings = fmap (fmap toPair) (topologicalSortComponents (depsOf <$> bindings))
  where
    keys = S.fromList (Name . unFieldName . fieldName <$> bindings)
    depsOf (Field (FieldName name) term) = (Name name, S.toList (S.intersection keys $ freeVariablesInTerm term))
    toPair name = (name, unbind name)
    unbind (Name name) = case L.filter (\f -> name == (unFieldName $ fieldName f)) bindings of
      [f] -> fieldTerm f
      _ -> TermLiteral $ LiteralString "Impossible!"

topologicalSortElements :: [Element] -> Either [[Name]] [Name]
topologicalSortElements els = topologicalSort $ adjlist <$> els
  where
    adjlist e = (elementName e, S.toList $ termDependencyNames False True True $ elementData e)

typeDependencyNames :: Type -> S.Set Name
typeDependencyNames = freeVariablesInType

unshadowVariables :: Term -> Term
unshadowVariables term = Y.fromJust $ flowStateValue $ unFlow (rewriteTermM rewrite term) (S.empty, M.empty) emptyTrace
  where
    rewrite recurse term = do
      (reserved, subst) <- getState
      case term of
        TermVariable v -> pure $ TermVariable $ Y.fromMaybe v $ M.lookup v subst
        TermFunction (FunctionLambda (Lambda v dom body)) -> if S.member v reserved
          then do
            v' <- freshName
            putState (S.insert v' reserved, M.insert v v' subst)
            body' <- recurse body
            putState (reserved, subst)
            pure $ TermFunction $ FunctionLambda $ Lambda v' dom body'
          else do
            putState (S.insert v reserved, subst)
            body' <- recurse body
            return $ TermFunction $ FunctionLambda $ Lambda v dom body'
        _ -> recurse term
    freshName = (\n -> Name $ "s" ++ show n) <$> nextCount "unshadow"

untype :: Term -> Term
untype term = case term of
  TermTyped (TypedTerm _ t) -> untype t
  _ -> term

-- | Find the variables (both bound and free) in a type expression, following a preorder traversal of the expression.
variablesInTypeOrdered :: Bool -> Type -> [Name]
variablesInTypeOrdered onlyBound = L.nub . vars -- Note: we rely on the fact that 'nub' keeps the first occurrence
  where
    vars t = case t of
      TypeLambda (LambdaType v body) -> v:(vars body)
      TypeVariable v -> if onlyBound then [] else [v]
      _ -> L.concat (vars <$> subtypes t)

-- | Where non-lambda terms with nonzero arity occur at the top level, turn them into lambdas,
--   also adding an appropriate type annotation to each new lambda.
wrapLambdas :: Term -> Flow Graph Term
wrapLambdas term = do
    typ <- requireTermType term
    let types = uncurryType typ
    let argTypes = L.init types
    let missing = missingArity (L.length argTypes) term
    return $ pad term (L.take missing argTypes) (toFunType $ L.drop missing types)
  where
    toFunType types = case types of
      [t] -> t
      (dom:rest) -> TypeFunction $ FunctionType dom $ toFunType rest
    missingArity arity term = if arity == 0
      then 0
      else case term of
        TermAnnotated (Annotated term2 _) -> missingArity arity term2
        TermLet (Let _ env) -> missingArity arity env
        TermFunction (FunctionLambda (Lambda _ _ body)) -> missingArity (arity - 1) body
        _ -> arity
    pad term doms cod = fst $ L.foldl newLambda (apps, cod) $ L.reverse variables
      where
        newLambda (body, cod) (v, dom) = (setTermType (Just ft) $ TermFunction $ FunctionLambda $ Lambda v Nothing body, ft)
          where
            ft = TypeFunction $ FunctionType dom cod
        apps = L.foldl (\lhs (v, _) -> TermApplication (Application lhs $ TermVariable v)) term variables
        variables = L.zip ((\i -> Name $ "a" ++ show i) <$> [1..]) doms
