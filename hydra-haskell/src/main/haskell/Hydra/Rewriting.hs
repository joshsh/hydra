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


alphaConvertTerm :: Name -> Term -> Term -> Term
alphaConvertTerm vold tnew = rewriteTerm rewrite id
  where
    rewrite recurse term = case term of
      TermFunction (FunctionLambda (Lambda v body)) -> if v == vold
        then term
        else recurse term
      TermVariable v -> if v == vold then tnew else TermVariable v
      _ -> recurse term

alphaConvertType :: Name -> Type -> Type -> Type
alphaConvertType vold tnew = rewriteType rewrite id
  where
    rewrite recurse typ = case typ of
      TypeLambda (LambdaType v body) -> if v == vold
        then typ
        else recurse typ
      TypeVariable v -> if v == vold then tnew else TypeVariable v
      _ -> recurse typ

boundVariablesInType :: Type -> S.Set Name
boundVariablesInType = foldOverType TraversalOrderPre fld S.empty
  where
    fld names typ = case typ of
      TypeLambda (LambdaType v _) -> S.insert v names
      _ -> names

elementsWithDependencies :: [Element] -> Flow Graph [Element]
elementsWithDependencies original = CM.mapM requireElement allDepNames
  where
    depNames = S.toList . termDependencyNames True False False . elementData
    allDepNames = L.nub $ (elementName <$> original) ++ (L.concat $ depNames <$> original)

freeVariablesInScheme :: TypeScheme -> S.Set Name
freeVariablesInScheme (TypeScheme vars t) = S.difference (freeVariablesInType t) (S.fromList vars)

isFreeIn :: Name -> Term -> Bool
isFreeIn v term = not $ S.member v $ freeVariablesInTerm term

-- | Implements specific rules which lift "forall" types out of subtype expressions
--   E.g. [\a.a] becomes \a.[a]
normalizePolytypes :: String -> Type -> Type
normalizePolytypes debugLabel = rewriteType (\recurse -> yank . recurse) id
  where
    yank typ = case typ of
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
        ((FieldType fname h):rest) -> normalize h $ \h1 -> normalize (yank $ TypeRecord (RowType tname ext rest)) $ helper h1
          where
            helper h1 t = case t of
              TypeRecord (RowType _ _ rest2) -> TypeRecord $ RowType tname ext ((FieldType fname h1):rest2)
              _ -> throwDebugException $ debugLabel ++ ": expected record type but found " ++ show t ++ " in " ++ show typ
      TypeSet st -> normalize st TypeSet
      TypeStream st -> normalize st TypeStream
      TypeSum types -> case types of
        [] -> TypeSum []
        (h:rest) -> normalize h $ \h1 -> normalize (yank $ TypeSum rest) $ \(TypeSum rest2) -> TypeSum $ h1:rest2
      TypeUnion (RowType tname ext fields) -> case fields of
        [] -> TypeUnion (RowType tname ext [])
        ((FieldType fname h):rest) -> normalize h $ \h1 -> normalize (yank $ TypeUnion (RowType tname ext rest)) $ helper h1
          where
            helper h1 t = case t of
              TypeUnion (RowType _ _ rest2) -> TypeUnion $ RowType tname ext ((FieldType fname h1):rest2)
              _ -> throwDebugException $ debugLabel ++ ": expected union type but found " ++ show t ++ " in " ++ show typ
      TypeWrap (Nominal name t) -> normalize t (TypeWrap . Nominal name)
      t -> t
    normalize subtype build = case subtype of
      TypeAnnotated (Annotated t ann) -> normalize t $ \t2 -> build $ TypeAnnotated $ Annotated t2 ann
      TypeLambda (LambdaType var body) -> TypeLambda $ LambdaType var $ yank $ build body
      t -> build t

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
  ((Term -> Flow s Term) -> Term -> (Flow s Term)) ->
  (Kv -> Flow s Kv) ->
  Term ->
  Flow s Term
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

rewriteTermMetaM :: (Kv -> Flow s Kv) -> Term -> Flow s Term
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
        TypeStream t -> TypeStream $ recurse t
        TypeSum types -> TypeSum (recurse <$> types)
        TypeUnion (RowType name extends fields) -> TypeUnion $ RowType name extends (forField <$> fields)
        TypeVariable v -> TypeVariable v
        TypeWrap (Nominal name t) -> TypeWrap $ Nominal name $ recurse t
      where
        forField f = f {fieldTypeType = recurse (fieldTypeType f)}

rewriteTypeM ::
  ((Type -> Flow s Type) -> Type -> (Flow s Type)) ->
  (Kv -> Flow s Kv) ->
  Type ->
  Flow s Type
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
        TypeStream t -> TypeStream <$> recurse t
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

topologicalSortElements :: [Element] -> Either [[Name]] [Name]
topologicalSortElements els = topologicalSort $ adjlist <$> els
  where
    adjlist e = (elementName e, S.toList $ termDependencyNames False True True $ elementData e)

typeDependencyNames :: Type -> S.Set Name
typeDependencyNames = freeVariablesInType
