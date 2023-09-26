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
alphaConvertTerm vold tnew = rewriteTerm rewrite
  where
    rewrite recurse term = case term of
      TermFunction (FunctionLambda (Lambda v body)) -> if v == vold
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
    TermRecord (Record n fields) -> TermRecord $ Record n $ forField recurse <$> fields
    TermSet s -> TermSet $ S.fromList $ recurse <$> S.toList s
    TermSum (Sum i s trm) -> TermSum $ Sum i s $ recurse trm
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
    TermRecord (Record n fields) -> TermRecord <$> (Record n <$> (CM.mapM (forField recurse) fields))
    TermSet s -> TermSet <$> (S.fromList <$> (CM.mapM recurse $ S.toList s))
    TermSum (Sum i s trm) -> TermSum <$> (Sum i s <$> recurse trm)
    TermUnion (Injection n field) -> TermUnion <$> (Injection n <$> forField recurse field)
    TermVariable v -> pure $ TermVariable v
    TermWrap (Nominal name t) -> TermWrap <$> (Nominal name <$> recurse t)
  where
    forField recurse f = do
      t <- recurse (fieldTerm f)
      return f {fieldTerm = t}

rewriteTermAnnotations :: (Kv -> Kv) -> Term -> Term
rewriteTermAnnotations f = rewriteTerm mapExpr
  where
    mapExpr recurse term = case term of
      TermAnnotated (Annotated term1 ann) -> TermAnnotated $ Annotated (recurse term1) (f ann)
      _ -> recurse term

rewriteTermAnnotationsM :: (Kv -> Flow s Kv) -> Term -> Flow s Term
rewriteTermAnnotationsM f = rewriteTermM mapExpr
  where
    mapExpr recurse term = case term of
      TermAnnotated (Annotated term1 ann) -> TermAnnotated <$> (Annotated <$> recurse term1 <*> f ann)
      _ -> pure term

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

rewriteTypeAnnotations :: (Kv -> Kv) -> Type -> Type
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
        TermFunction (FunctionLambda (Lambda var body)) ->
          if S.member var (freeVariablesInTerm body)
            then case stripTerm rhs of
              TermVariable v -> simplifyTerm $ substituteVariable var v body
              _ -> term
            else simplifyTerm body
        _ -> term
      _ -> term

simplifyUniversalTypes :: Type -> Type
simplifyUniversalTypes = rewriteType f
  where
    f recurse t = case recurse t of
      -- Caution: time complexity
      TypeLambda (LambdaType v body) -> if S.member v (freeVariablesInType body)
        then t
        else body
      _ -> t

substituteVariable :: Name -> Name -> Term -> Term
substituteVariable from to = rewriteTerm replace
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
