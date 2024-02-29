{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- Implementation of Hindley Milner algorithm W 
-- to system F translation by Ryan Wisnesky.
-- License: Apache 2.0 https://www.apache.org/licenses/LICENSE-2.0 

module Hydra.AlgorithmW where

import qualified Hydra.Core as Core
import qualified Hydra.Graph as Graph
import qualified Hydra.Dsl.Literals as Literals
import qualified Hydra.Dsl.LiteralTypes as LiteralTypes
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types
import Hydra.Sources.Libraries
import Hydra.Basics
import Hydra.Strip
import Hydra.Substitution (normalizeBoundTypeVariablesInSystemFTerm)

import Control.Monad.Error
import Control.Monad.State

import qualified Data.List as L
import qualified Data.Map as M
import qualified Control.Monad as CM

------------------------
-- STLC

type Var = String

-- A typed primitive corresponds to the Hydra primitive of the same name
data TypedPrimitive = TypedPrimitive Core.Name TypSch deriving (Eq)

data Prim
 = Lit Core.Literal
 | TypedPrim TypedPrimitive
 | If0
 | Fst | Snd | Pair | TT
 | Nil | Cons | FoldList  
 | FF | Inl | Inr | Case 
 deriving Eq
 
instance Show Prim where
  show (Lit l) = show l
  show (TypedPrim (TypedPrimitive name _)) = Core.unName name ++ "()"
  show FoldList = "fold"
  show Fst = "fst"
  show Snd = "snd"
  show Nil = "nil"
  show Cons = "cons"
  show TT = "tt"
  show FF = "ff"
  show Inl = "inl"
  show Inr = "inr"
  show Case = "case"
  show If0 = "if0" 
  show Pair = "pair"

data Expr = Const Prim
 | Var Var
 | App Expr Expr
 | Abs Var Expr
 | Let Var Expr Expr
 | Letrec [(Var, Expr)] Expr
 | Prod [Expr]
 | Sum Int Int Expr
 deriving (Eq)
-- deriving (Eq, Show)

instance Show Expr where
  show (Const p) = show p
  show (Var v) = v
  show (App (App (App a' a) b) b') = "(" ++ show a' ++ " " ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (App (App a b) b') = "(" ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (Abs a b) = "(\\" ++ a ++ ". " ++ show b ++ ")"
  show (Let a b c) = "let " ++ a ++ " = " ++ show b ++ " in " ++ show c
  show (Letrec ab c) = "letrecs " ++ d ++ show c
    where d = foldr (\(p, q) r -> p ++ " = " ++ show q ++ " \n\t\t" ++ r) "in " ab
  show (Prod els) = "(" ++ L.intercalate ", " (show <$> els) ++ ")"
  show (Sum i n e) = "in[" ++ show i ++ "/" ++ show n ++ "](" ++ show e ++ ")"

data MTy = TyVar Var
  | TyLit Core.LiteralType
  | TyList MTy 
  | TyFn MTy MTy
  | TyProd MTy MTy
  | TySum MTy MTy
  | TyUnit 
  | TyVoid
  | TyProdN [MTy]
  | TySumN [MTy]
 deriving (Eq)
 
instance Show MTy where
  show (TyLit lt) = case lt of
    Core.LiteralTypeInteger it -> L.drop (L.length "IntegerType") $ show it
    Core.LiteralTypeFloat ft -> L.drop (L.length "FloatType") $ show ft
    _ -> L.drop (L.length "LiteralType") $ show lt
  show (TyVar v) = v
  show (TyList t) = "(List " ++ (show t) ++ ")"
  show (TyFn t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TyProd t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++ ")"
  show (TySum t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++  ")"
  show TyUnit = "Unit"
  show TyVoid = "Void"
  show (TyProdN tys) = "*[" ++ L.intercalate ", " (show <$> tys) ++ "]"
  show (TySumN tys) = "*[" ++ L.intercalate ", " (show <$> tys) ++ "]"

instance Show TypSch where
  show (Forall [] t) = show t
  show (Forall x t) = "forall " ++ d ++ show t
   where d = foldr (\p q -> p ++ " " ++ q) ", " x
  
data TypSch = Forall [Var] MTy
 deriving Eq 

------------------------
-- System F

data FExpr = FConst Prim
 | FVar Var
 | FApp FExpr FExpr
 | FAbs Var FTy FExpr
 | FTyApp FExpr [FTy]
 | FTyAbs [Var] FExpr 
 | FLetrec [(Var, FTy, FExpr)] FExpr
 | FProd [FExpr]
 | FSum Int Int FExpr
 deriving (Eq)
-- deriving (Eq, Show)

instance Show FExpr where
  show (FConst p) = show p
  show (FVar v) = v
  show (FTyApp e t) = "(" ++ show e ++ " " ++ show t ++ ")"
  show (FApp (FApp (FApp a' a) b) b') = "(" ++ show a' ++ " " ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (FApp (FApp a b) b') = "(" ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (FApp a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (FAbs a t b) = "(\\" ++ a ++ ":" ++ show t ++ ". " ++ show b ++ ")"
  show (FLetrec ab c) = "letrecs " ++ d ++ show c
    where d = foldr (\(p, t, q) r -> p ++ ":" ++ show t ++ " = " ++ show q ++ " \n\t\t" ++ r) "in " ab
  show (FTyAbs ab c) = "(/\\" ++ d ++ show c ++ ")"
    where d = foldr (\p r -> p ++ " " ++ r) ". " ab
  show (FProd els) = "*[" ++ L.intercalate ", " (show <$> els) ++ "]"
  show (FSum i n e) = "in[" ++ show i ++ "/" ++ show n ++ "](" ++ show e ++ ")"

data FTy = FTyVar Var
  | FTyLit Core.LiteralType
  | FTyList FTy 
  | FTyFn FTy FTy
  | FTyProd FTy FTy
  | FTySum FTy FTy
  | FTyUnit 
  | FTyVoid
  | FForall [Var] FTy
  | FTyProdN [FTy]
  | FTySumN [FTy]
 deriving (Eq)
 
instance Show FTy where
  show (FTyLit lt) = show $ TyLit lt
  show (FTyVar v) = v
  show (FTyList t) = "(List " ++ (show t) ++ ")"
  show (FTyFn t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (FTyProd t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++  ")"
  show (FTySum t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++  ")"
  show FTyUnit = "Unit"
  show FTyVoid = "Void"
  show (FForall x t) = "(forall " ++ d ++ show t ++ ")"
   where d = foldr (\p q -> p ++ " " ++ q) ", " x
  show (FTyProdN tys) = "*[" ++ L.intercalate ", " (show <$> tys) ++ "]"
  show (FTySumN tys) = "+[" ++ L.intercalate ", " (show <$> tys) ++ "]"

mTyToFTy :: MTy -> FTy 
mTyToFTy (TyVar v) = FTyVar v
mTyToFTy (TyLit lt) = FTyLit lt
mTyToFTy TyUnit = FTyUnit
mTyToFTy TyVoid = FTyVoid
mTyToFTy (TyList x) = FTyList $ mTyToFTy x
mTyToFTy (TyFn x y) = FTyFn (mTyToFTy x) (mTyToFTy y)
mTyToFTy (TyProd x y) = FTyProd (mTyToFTy x) (mTyToFTy y)
mTyToFTy (TySum x y) = FTySum (mTyToFTy x) (mTyToFTy y)
mTyToFTy (TyProdN tys) = FTyProdN (mTyToFTy <$> tys)
mTyToFTy (TySumN tys) = FTySumN (mTyToFTy <$> tys)

tyToFTy :: TypSch -> FTy 
tyToFTy (Forall [] t) = mTyToFTy t
tyToFTy (Forall vs t) = FForall vs (mTyToFTy t)

--------------------
-- Contexts 

type Ctx = [(Var, TypSch)]

class Vars a where
  vars :: a -> [Var]

instance Vars Ctx where
 vars [] = []
 vars ((v,t):l) = vars t ++ vars l

instance Vars TypSch where
 vars (Forall vs t) = filter (\v -> not $ elem v vs) (vars t) 

instance Vars MTy where
 vars (TyVar v) = [v]
 vars (TyList t) = vars t 
 vars (TyFn t1 t2) = vars t1 ++ vars t2
 vars TyUnit = []
 vars TyVoid = []
 vars (TyProd t1 t2) = vars t1 ++ vars t2
 vars (TySum t1 t2) = vars t1 ++ vars t2
 vars (TyLit _) = []
 vars (TyProdN tys) = L.concat (vars <$> tys)
 vars (TySumN tys) = L.concat (vars <$> tys)

primTy :: Prim -> TypSch
primTy (Lit l) = Forall [] $ TyLit $ literalType l
primTy (TypedPrim (TypedPrimitive _ forall)) = forall
primTy Fst = Forall ["x", "y"] $ (TyProd (TyVar "x") (TyVar "y")) `TyFn` (TyVar "x")
primTy Snd = Forall ["x", "y"] $ (TyProd (TyVar "x") (TyVar "y")) `TyFn` (TyVar "y")
primTy Nil = Forall ["t"] $ TyList (TyVar "t")
primTy Cons = Forall ["t"] $ TyFn (TyVar "t") (TyFn (TyList (TyVar "t")) (TyList (TyVar "t")))
primTy TT = Forall [] TyUnit
primTy FF = Forall ["t"] $ TyFn TyVoid (TyVar "t")
primTy Inl = Forall ["x", "y"] $ (TyVar "x") `TyFn` (TyProd (TyVar "x") (TyVar "y"))  
primTy Inr = Forall ["x", "y"] $ (TyVar "y") `TyFn` (TyProd (TyVar "x") (TyVar "y"))
primTy Pair = Forall ["x", "y"] $ (TyFn (TyVar "x") (TyFn (TyVar "y") (TyProd (TyVar "x") (TyVar "y"))))
primTy If0 = Forall [] $ (TyLit LiteralTypes.int32) `TyFn` ((TyLit LiteralTypes.int32) `TyFn` ((TyLit LiteralTypes.int32) `TyFn` (TyLit LiteralTypes.int32)))
primTy FoldList = Forall ["a", "b"] $ p `TyFn` ((TyVar "b") `TyFn` ((TyList $ TyVar "a") `TyFn` (TyVar "b")))
 where p = TyVar "b" `TyFn` (TyVar "a" `TyFn` TyVar "b")
primTy Case = Forall ["x", "y", "z"] $ (TySum (TyVar "x") (TyVar "y")) `TyFn` (l `TyFn` (r `TyFn` (TyVar "z"))) 
 where l = (TyVar "x") `TyFn` (TyVar "z")
       r = (TyVar "y") `TyFn` (TyVar "z")
  
 -- add eval? 
-----------------------------
-- Substitution

type Subst = [(Var, MTy)]

idSubst :: Subst 
idSubst = []

o :: Subst -> Subst -> Subst
o f g = addExtra ++ map h g
 where h (v, g') = (v, subst f g')
       addExtra = filter (\(v,f')-> case lookup v g of 
                                      Just y  -> False 
                                      Nothing -> True) f
oMany :: [Subst] -> Subst
oMany = L.foldl o []

class Substable a where
  subst :: Subst -> a -> a
  
instance Substable MTy where
 subst f (TyLit lt) = TyLit lt
 subst f TyUnit = TyUnit 
 subst f TyVoid = TyVoid
 subst f (TyList t) = TyList $ subst f t 
 subst f (TyFn t1 t2) = TyFn (subst f t1) (subst f t2) 
 subst f (TyProd t1 t2) = TyProd  (subst f t1) (subst f t2)
 subst f (TySum t1 t2) = TySum  (subst f t1) (subst f t2)
 subst f (TyVar v) = case lookup v f of
                      Nothing -> TyVar v
                      Just y -> y
 subst f (TyProdN tys) = TyProdN (subst f <$> tys)
 subst f (TySumN tys) = TySumN (subst f <$> tys)

instance Substable FTy where
 subst f (FTyLit lt) = FTyLit lt
 subst f FTyUnit = FTyUnit 
 subst f FTyVoid = FTyVoid
 subst f (FTyList t) = FTyList $ subst f t 
 subst f (FTyFn t1 t2) = FTyFn (subst f t1) (subst f t2) 
 subst f (FTyProd t1 t2) = FTyProd  (subst f t1) (subst f t2)
 subst f (FTySum t1 t2) = FTySum  (subst f t1) (subst f t2)
 subst f (FTyVar v) = case lookup v f of
                        Nothing -> FTyVar v
                        Just y -> mTyToFTy y
 subst f (FForall vs t) = FForall vs $ subst phi' t                        
  where phi' = filter (\(v,f')-> not (elem v vs)) f
 subst f (FTyProdN tys) = FTyProdN (subst f <$> tys)
 subst f (FTySumN tys) = FTySumN (subst f <$> tys)

instance Substable TypSch where
 subst f (Forall vs t) = Forall vs $ subst f' t 
   where f' = filter (\(v,t')-> elem v vs) f

instance Substable Ctx where
 subst phi g = map (\(k,v)->(k, subst phi v)) g

instance Substable FExpr where 
 subst phi (FConst p) = FConst p
 subst phi (FVar p) = FVar p
 subst phi (FApp p q) = FApp (subst phi p) (subst phi q)
 subst phi (FAbs p t q) = FAbs p (subst phi t) (subst phi q)
 subst phi (FTyApp p q) = FTyApp (subst phi p) (map (subst phi) q) 
 subst phi (FTyAbs vs p) = FTyAbs vs (subst phi' p)
  where phi' = filter (\(v,f')-> not (elem v vs)) phi
 subst phi (FLetrec vs p) = FLetrec (map (\(k,t,v)->(k,subst phi t, subst phi v)) vs) (subst phi p)
 subst phi (FProd els) = FProd (subst phi <$> els)
 subst phi (FSum i n e) = FSum i n $ subst phi e

subst' :: [(Var,FTy)] -> FTy -> FTy
subst' f (FTyLit lt) = FTyLit lt
subst' f FTyUnit = FTyUnit 
subst' f FTyVoid = FTyVoid
subst' f (FTyList t) = FTyList $ subst' f t 
subst' f (FTyFn t1 t2) = FTyFn (subst' f t1) (subst' f t2) 
subst' f (FTyProd t1 t2) = FTyProd  (subst' f t1) (subst' f t2)
subst' f (FTySum t1 t2) = FTySum  (subst' f t1) (subst' f t2)
subst' f (FTyVar v) = case lookup v f of
                        Nothing -> FTyVar v
                        Just y -> y
subst' f (FForall vs t) = FForall vs $ subst' f' t                         
 where f' = filter (\(v,f')-> not (elem v vs)) f
subst' f (FTyProdN tys) = FTyProdN (subst' f <$> tys)
subst' f (FTySumN tys) = FTySumN (subst' f <$> tys)

------------------------------------
-- Type checking for F

open :: [Var] -> [FTy] -> FTy -> Either String FTy
open vs ts e | length vs == length ts = return $ subst' (zip vs ts) e
             | otherwise = throwError "Cannot open"

typeOf :: [Var] -> [(Var,FTy)] -> FExpr -> Either String FTy
typeOf tvs g (FVar x) = case lookup x g of  
  Nothing -> throwError $ "unbound var: " ++ x
  Just y -> return y
typeOf tvs g (FConst p) = return $ tyToFTy $ primTy p  
typeOf tvs g (FApp a b) = do { t1 <- typeOf tvs g a
                             ; t2 <- typeOf tvs g b
                             ; case t1 of
                                (FTyFn p q) -> if p == t2 
                                               then return q 
                                               else throwError $ "In " ++ (show $ FApp a b) ++ " expected " ++ show p ++ " given " ++ show t2
                                v -> throwError $ "In " ++ show (FApp a b) ++ " not a fn type: " ++ show v }
typeOf tvs g (FAbs x t e) = do { t1 <- typeOf tvs ((x,t):g) e
                               ; return $ t `FTyFn` t1 }
typeOf tvs g (FTyAbs vs e) = do { t1 <- typeOf (vs++tvs) g e
                                ; return $ FForall vs t1 }
typeOf tvs g (FTyApp e ts) = do { t1 <- typeOf tvs g e
                                ; case t1 of
                                    FForall vs t -> open vs ts t 
                                    v -> throwError $ "not a forall type: " ++ show v }  
typeOf tvs g (FLetrec es e) = do { let g' = map (\(k,t,e)->(k,t)) es
                                 ; est <- mapM (\(_,_,v)->typeOf tvs (g'++g) v) es
                                 ; if est == (snd $ unzip g') 
                                   then typeOf tvs g' e 
                                   else throwError $ "Disagree: " ++ show est ++ " and " ++ (show $ snd $ unzip g') }                                     
typeOf tvs g (FProd els) = FTyProdN <$> CM.mapM (typeOf tvs g) els

-----------------------------
-- Unification

-- mgu = most general unifier
mgu :: MTy -> MTy -> E Subst
mgu (TyLit lt1) (TyLit lt2) = if lt1 == lt2
  then return []
  else throwError $ "Cannot unify literal types " ++ show lt1 ++ " and " ++ show lt2
mgu (TyList a) (TyList b) = mgu a b
mgu TyUnit TyUnit = return []
mgu TyVoid TyVoid = return []
mgu (TyProd a b) (TyProd a' b') = do { s <- mgu a a' ; s' <- mgu (subst s b) (subst s b'); return $ s' `o` s }
mgu (TySum  a b) (TySum  a' b') = do { s <- mgu a a' ; s' <- mgu (subst s b) (subst s b'); return $ s' `o` s }
mgu (TyProdN tys) (TyProdN tys') = mguMany tys tys'
mgu (TySumN tys) (TySumN tys') = mguMany tys tys'
mgu (TyFn a b) (TyFn a' b') = do { s <- mgu a a' ; s' <- mgu (subst s b) (subst s b'); return $ s' `o` s }
mgu (TyVar a) (TyVar b) | a == b = return []
mgu (TyVar a) b = do { occurs a b; return [(a, b)] }
mgu a (TyVar b) = mgu (TyVar b) a
mgu a b = throwError $ "cannot unify " ++ show a ++ " with " ++ show b 

mguMany :: [MTy] -> [MTy] -> E Subst
mguMany [] [] = return idSubst
mguMany (a:as) (b:bs) = do { f <- mgu a b; s <- mguMany (map (subst f) as) (map (subst f) bs); return $ s `o` f }

occurs :: Var -> MTy -> E ()
occurs v (TyLit _) = return ()
occurs v (TyList l) = occurs v l
occurs v TyUnit = return ()
occurs v TyVoid = return ()       
occurs v (TyFn   a b) = do { occurs v a; occurs v b }
occurs v (TyProd a b) = do { occurs v a; occurs v b }
occurs v (TySum  a b) = do { occurs v a; occurs v b }
occurs v (TyProdN tys) = do { CM.mapM (occurs v) tys; return () }
occurs v (TySumN tys) = do { CM.mapM (occurs v) tys; return() }
occurs v (TyVar v') | v == v' = throwError $ "occurs check failed"
                    | otherwise = return ()

-----------------------------
-- Algorithm W 

type E = ErrorT String (State Int)
type M a = E (Subst, a)

fresh :: E MTy
fresh = do { s <- get; put (s + 1); return $ TyVar $ "v" ++ show s }

inst :: TypSch -> E (MTy,[MTy])
inst (Forall vs ty) = do { vs' <- mapM (\_->fresh) vs; return $ (subst (zip vs vs') ty,  vs') } 

gen :: Ctx -> MTy -> (TypSch, [Var])
gen g t = (Forall vs t , vs)
 where vs = L.nub $ filter (\v -> not $ elem v (vars g)) (vars t)

fTyApp x [] = x
fTyApp x y = FTyApp x y

fTyAbs [] x = x
fTyAbs x y = FTyAbs x y

w :: Ctx -> Expr -> M (MTy, FExpr)
w g (Const p) = do { (t,vs) <- inst $ primTy p; return (idSubst, (t, fTyApp (FConst p) $ map mTyToFTy vs)) }
 where Forall vs t' = primTy p
w g (Var x) = case lookup x g of 
                Nothing -> throwError $ "Unknown var: " ++ (show x)
                Just s -> do { (t,vs) <- inst s; return (idSubst, (t, fTyApp (FVar x) $ map mTyToFTy vs)) }
w g (App e0 e1) = do { (s0, (t0, a)) <- w g e0
                     ; (s1, (t1, b)) <- w (subst s0 g) e1 
                     ; t' <- fresh
                     ; s2 <-  (subst s1 t0) `mgu` (t1 `TyFn` t') 
                     ; return (s2 `o` s1 `o` s0, (subst s2 t', FApp (subst (s2 `o` s1) a) (subst s2 b))) } 
w g (Abs x e) = do { t  <- fresh
                   ; (s, (t', a)) <- w ((x, (Forall [] t)):g) e                      
                   ; return (s, (TyFn (subst s t) t', FAbs x (mTyToFTy $ subst s t) a)) }
w g (Let x e0 e1) = do { (s0, (t, a)) <- w g e0
                       ; let (tt,vs) = gen (subst s0 g) t
                       ; (s1, (t', b)) <- w ((x,tt):subst s0 g) e1
                       ; return (s1 `o` s0, (t', FApp (FAbs x (tyToFTy $ subst s1 tt) b) (fTyAbs vs a))) }
w g (Letrec xe0 e1) = do { t0s <- mapM (\(k,v) -> do { f <- fresh; return (k, f) }) xe0
                         ; let g' = map (\(k,v) -> (k, Forall [] v)) t0s ++ g
                         ; (s0, (ts,e0Xs)) <- w' g' xe0
                         ; s' <- mguMany (map (\(_,v) -> subst s0 v) t0s) ts
                         ; let g''' = subst (s' `o` s0) g'
                               g''  = map (\(k,t) -> (k, fst $ gen g''' (subst s' t))) $ zip (fst $ unzip xe0) ts
                               g''X = map (\(k,t) -> (k, gen g''' (subst s' t))) $ zip (fst $ unzip xe0) ts
                         ; (s1, (t',e1X)) <- w (g'' ++ g''') e1
                         ; let mmm = map (\((x,(ww,ww2)),e0X)->(x, (fTyApp (FVar x) $ map FTyVar ww2))) $  zip g''X e0Xs
                         ; let e0X's =  map (\((x,(ww,ww2)),e0X)->(x,ww,ww2, subst'' mmm e0X)) $ zip g''X e0Xs  
                         ; let e0X''s = map (\(x,ww,ww2,e) -> (x,ww,ww2,fTyAbs ww2 e)) e0X's 
                         ; let bs = map (\(x,ww,ww2,e0X'') -> (x, subst s1 $ tyToFTy ww, subst (s' `o` s1) e0X'')) e0X''s                
                         ; return (s1 `o` s' `o` s0, (t', FLetrec bs e1X)) }       
 where w' g [] = return (idSubst, ([], [])) 
       w' g  ((k,v):tl) = do { (u,(u', j)) <- w g v
                             ; (r,(r', h)) <- w' (subst u g ) tl
                             ; return (r `o` u, ((subst r u'):r', (subst r j):h)) }
w g (Prod els) = do
  ws <- CM.mapM (w g) els
  let tys = fst . snd <$> ws
  let es = snd . snd <$> ws
  return (oMany (fst <$> ws), (TyProdN tys, FProd es))


-- Save the following for n-ary lists:
--w g (List els) = do
--    v <- fresh
--    (g1, s1, tys, es) <- CM.foldM wnext (g, [], [v], []) $ L.reverse els
--    s2 <- mguMany (L.init tys) (L.tail tys)
--    return (s1 `o` s2, (TyList tys, FList es))
--  where
--    wnext (g0, s0, tys, es) e0 = do
--      (s1, (t, e1)) <- w g0 e0
--      let s2 = s0 `o` s1
--      let g1 = subst s2 g0
--      return (g1, s2, t:tys, e1:es)

subst'' :: [(Var, FExpr)] -> FExpr -> FExpr
subst'' phi (FConst c) = FConst c
subst'' phi (FVar v') = case lookup v' phi of
                         Just y -> y
                         Nothing -> FVar v'
subst'' phi (FApp a b) = FApp (subst'' phi a) (subst'' phi b)
subst'' phi (FAbs v' a b) = FAbs v' a $ subst'' phi' b 
 where phi' = filter (\(k,v) -> not (k == v')) phi 
subst'' phi (FTyApp a ts) = FTyApp (subst'' phi a) ts
subst'' phi (FTyAbs vs a) = FTyAbs vs $ subst'' phi a
subst'' phi (FLetrec es e) = FLetrec (map (\(k,t,f)->(k,t,subst'' phi' f)) es) (subst'' phi' e)
 where phi' = filter (\(k,v) -> not (elem k ns)) phi
       (ns,ts,es') = unzip3 es 
subst'' phi (FProd els) = FProd (subst'' phi <$> els)
subst'' phi (FSum i n e) = FSum i n $ subst'' phi e

----------------------------------------
-- Hydra Core support

-- A minimal Hydra graph container for use in these translation functions
data HydraContext = HydraContext (M.Map Core.Name Graph.Primitive)

natType = TyLit LiteralTypes.int32
constPred = Const $ TypedPrim $ TypedPrimitive _math_neg $ Forall [] $ TyFn natType natType
constSucc = Const $ TypedPrim $ TypedPrimitive _math_neg $ Forall [] $ TyFn natType natType

-- Note: no support for @wisnesky's Prim constructors other than PrimStr, PrimNat, Cons, and Nil
hydraTermToStlc :: HydraContext -> Core.Term -> Either String Expr
hydraTermToStlc context term = case term of
    Core.TermApplication (Core.Application t1 t2) -> App <$> toStlc t1 <*> toStlc t2
    Core.TermFunction f -> case f of
      Core.FunctionLambda (Core.Lambda (Core.Name v) _ body) -> Abs <$> pure v <*> toStlc body
      Core.FunctionPrimitive name -> do
        prim <- case M.lookup name prims of
          Nothing -> Left $ "no such primitive: " ++ Core.unName name
          Just p -> Right p
        ts <- hydraTypeToTypeScheme $ Graph.primitiveType prim
        return $ Const $ TypedPrim $ TypedPrimitive name ts
    Core.TermLet (Core.Let bindings env) -> Letrec <$> CM.mapM fieldToStlc bindings <*> toStlc env
      where
        fieldToStlc (Core.Field (Core.FieldName v) term) = do
          s <- toStlc term
          return (v, s)
    Core.TermList els -> do
      sels <- CM.mapM toStlc els
      return $ foldr (\el acc -> App (App (Const Cons) el) acc) (Const Nil) sels
    Core.TermLiteral lit -> pure $ Const $ Lit lit
    Core.TermProduct els -> Prod <$> (CM.mapM toStlc els)
--    Core.TermProduct els -> do
--      sels <- CM.mapM toStlc els
--      if L.length sels >= 2
--        then let rev = L.reverse sels
--             in return $ L.foldl (\a e -> pair e a) (pair (rev !! 1) (rev !! 0)) $ L.drop 2 rev
--        else Left $ "Unary and nullary products are not yet supported"
    Core.TermVariable (Core.Name v) -> pure $ Var v
    _ -> Left $ "Unsupported term: " ++ show term
  where
    HydraContext prims = context
    toStlc = hydraTermToStlc context
    pair a b = App (App (Const Pair) a) b

hydraTypeToTypeScheme :: Core.Type -> Either String TypSch
hydraTypeToTypeScheme typ = do
    let (boundVars, baseType) = splitBoundVars [] typ
    ty <- toStlc baseType
    return $ Forall (Core.unName <$> boundVars) ty
  where
    toStlc typ = case stripType typ of
      Core.TypeFunction (Core.FunctionType dom cod) -> TyFn <$> toStlc dom <*> toStlc cod
      Core.TypeList et -> TyList <$> toStlc et
      Core.TypeLiteral lt -> pure $ TyLit lt
--      TypeMap MapType |
--      TypeOptional Type |
      Core.TypeProduct types -> if L.length types == 0
        then pure TyUnit
        else if L.length types == 1
          then Left $ "unary products are not yet supported"
          else do
            stypes <- CM.mapM toStlc types
            let rev = L.reverse stypes
            return $ L.foldl (\a e -> TyProd e a) (TyProd (rev !! 1) (rev !! 0)) $ L.drop 2 rev
--      TypeRecord RowType |
--      TypeSet Type |
--      TypeStream Type |
      Core.TypeSum types -> if L.length types == 0
        then pure TyVoid
        else if L.length types == 1
          then Left $ "unary sums are not yet supported"
          else do
            stypes <- CM.mapM toStlc types
            let rev = L.reverse stypes
            return $ L.foldl (\a e -> TySum e a) (TySum (rev !! 1) (rev !! 0)) $ L.drop 2 rev
--      TypeUnion RowType |
      Core.TypeVariable name -> pure $ TyVar $ Core.unName name
--      TypeWrap (Nominal Type)
      _ -> Left $ "unsupported type: " ++ show typ
    splitBoundVars vars typ = case stripType typ of
      Core.TypeLambda (Core.LambdaType v body) -> (v:vars', typ')
        where
          (vars', typ') = splitBoundVars vars body
      _ -> (vars, typ)

systemFExprToHydra :: FExpr -> Either String Core.Term
systemFExprToHydra expr = case expr of
  FConst prim -> case prim of
    Lit lit -> pure $ Core.TermLiteral lit
    TypedPrim (TypedPrimitive name _) -> pure $ Core.TermFunction $ Core.FunctionPrimitive name
    Nil -> pure $ Core.TermList []
    _ -> Left $ "Unsupported primitive: " ++ show prim
    -- Note: other prims are unsupported
  FVar v -> pure $ Core.TermVariable $ Core.Name v
  FApp e1 e2 -> case e1 of
    FApp (FTyApp (FConst Cons) _) hd -> do
        els <- CM.mapM systemFExprToHydra (hd:(gather e2))
        return $ Core.TermList els -- TODO: include inferred type
      where
        gather e = case e of
          FTyApp (FConst Nil) _ -> []
          FApp (FApp (FTyApp (FConst Cons) _) hd) tl -> hd:(gather tl)
    FTyApp (FConst Pair) _ -> do
--        els <- CM.mapM systemFExprToHydra (gather expr)
        els <- pure []
        return $ Core.TermProduct els -- TODO: include inferred type
      where
        gather e = case e of
          FApp (FApp (FTyApp (FConst Pair) _) el) arg -> el:(gather arg)
          _ -> [e]
    _ -> Core.TermApplication <$> (Core.Application <$> systemFExprToHydra e1 <*> systemFExprToHydra e2)
  FAbs v dom e -> do
    term <- systemFExprToHydra e
    hdom <- systemFTypeToHydra dom
    return $ Core.TermFunction $ Core.FunctionLambda (Core.Lambda (Core.Name v) (Just hdom) term)
  FTyAbs params body -> do
    hbody <- systemFExprToHydra body
    return $ L.foldl (\t v -> Core.TermTypeAbstraction $ Core.TypeAbstraction (Core.Name v) t) hbody $ L.reverse params
  FTyApp fun args -> do
    hfun <- systemFExprToHydra fun
    hargs <- CM.mapM systemFTypeToHydra args
    return $ L.foldl (\t a -> Core.TermTypeApplication $ Core.TypedTerm a t) hfun $ L.reverse hargs
  FLetrec bindings env -> Core.TermLet <$>
      (Core.Let <$> CM.mapM bindingToHydra bindings <*> systemFExprToHydra env)
    where
      bindingToHydra (v, ty, term) = do
        hterm <- systemFExprToHydra term
        htyp <- systemFTypeToHydra ty
        return $ Core.Field (Core.FieldName v) $ Core.TermTyped $ Core.TypedTerm htyp hterm
  FProd els -> Core.TermProduct <$> (CM.mapM systemFExprToHydra els)
  FSum i n e -> Core.TermSum <$> (Core.Sum i n <$> systemFExprToHydra e)

systemFTypeToHydra :: FTy -> Either String Core.Type
systemFTypeToHydra ty = case ty of
  FTyVar v -> pure $ Core.TypeVariable $ Core.Name v
  FTyLit lt -> pure $ Core.TypeLiteral lt
  FTyList lt -> Core.TypeList <$> systemFTypeToHydra lt
  FTyFn dom cod -> Core.TypeFunction <$> (Core.FunctionType <$> systemFTypeToHydra dom <*> systemFTypeToHydra cod)
  FTyProd t1 t2 -> Core.TypeProduct <$> CM.mapM systemFTypeToHydra (t1:(componentsTypesOf t2))
    where
      componentsTypesOf t = case t of
        FTyProd t1 t2 -> t1:(componentsTypesOf t2)
        _ -> [t]
  FTySum t1 t2 -> Core.TypeSum <$> CM.mapM systemFTypeToHydra (t1:(componentsTypesOf t2))
    where
      componentsTypesOf t = case t of
        FTySum t1 t2 -> t1:(componentsTypesOf t2)
        _ -> [t]
  FTyUnit -> pure $ Core.TypeProduct []
  FTyVoid -> pure $ Core.TypeSum []
  FForall vars body -> do
    body' <- systemFTypeToHydra body
    return $ L.foldl (\e v -> Core.TypeLambda $ Core.LambdaType (Core.Name v) e) body' $ L.reverse vars
  FTyProdN tys -> Core.TypeProduct <$> (CM.mapM systemFTypeToHydra tys)
  FTySumN tys -> Core.TypeSum <$> (CM.mapM systemFTypeToHydra tys)

inferWithAlgorithmW :: HydraContext -> Core.Term -> IO Core.Term
inferWithAlgorithmW context term = do
    stlc <- case hydraTermToStlc context (wrap term) of
       Left err -> fail err
       Right t -> return t
    (fexpr, _) <- inferExpr stlc
    case systemFExprToHydra fexpr of
      Left err -> fail err
      Right t -> normalizeBoundTypeVariablesInSystemFTerm <$> unwrap t
  where
    sFieldName = Core.FieldName "tempVar"
    wrap term = Core.TermLet $ Core.Let ([Core.Field sFieldName term]) $
      Core.TermLiteral $ Core.LiteralString "tempEnvironment"
    unwrap term = case term of
      Core.TermLet (Core.Let bindings _) -> case bindings of
        [(Core.Field fname t)] -> if fname == sFieldName
          then pure t
          else fail "expected let binding matching input"
        _ -> fail "expected let bindings"

inferExpr :: Expr -> IO (FExpr, FTy)
inferExpr t = case (fst $ runState (runErrorT (w [] t)) 0) of
  Left e -> fail $ "inference error: " ++ e
  Right (_, (ty, f)) -> case (typeOf [] [] f) of
    Left err -> fail $ "type error: " ++ err
    Right tt -> if tt == mTyToFTy ty
      then return (f, tt)
      else fail "no match"

----------------------------------------
-- Main

tests = [test_0, test_1, test_2, test_3, test_4, test_5, test_6, test_7, test_8, test_10, test_11, test_12]

testOne :: Expr -> IO ()
testOne t = do { putStrLn $ "Untyped input: "
               ; putStrLn $ "\t" ++  show t 
               ; let out = fst $ runState (runErrorT (w [] t)) 0
               ; case out of
                   Left  e -> putStrLn $ "\t" ++ "err: " ++ e
                   Right (s, (ty, f)) -> do { 
                                            ; putStrLn $ "\nType inferred by Hindley-Milner: "
                                            ; putStrLn $ "\t" ++ show ty
                                            ; putStrLn "\nSystem F translation: " 
                                            ; putStrLn $ "\t" ++ show f
                                            ; putStrLn "\nSystem F type: " 
                                            ; case (typeOf [] [] f) of
                                               Left err -> putStrLn $ "\t" ++  "err: " ++ err
                                               Right tt -> do { putStrLn $ " \t" ++ show tt
                                                              ; if tt == mTyToFTy ty then return () else putStrLn "** !!! NO MATCH" } }
               ; putStrLn ""
               ; putStrLn "------------------------" 
               ; putStrLn ""  }

main = mapM testOne tests 

letrec' x e f = Letrec [(x,e)] f

test_0 :: Expr
test_0 = Abs "x" $ Var "x"

test_1 :: Expr
test_1 = Letrec [("foo", Abs "x" $ Var "x")] $ Const $ Lit $ Literals.int32 42

test_2 :: Expr
test_2 =  Let "f" ( (Abs "x" (Var "x"))) $ App (Var "f")  (Const $ Lit $ Literals.int32 0)
 where sng0 = App (Var "sng") (Const $ Lit $ Literals.int32 0)
       sngAlice = App (Var "sng") (Const $ Lit $ Literals.string "alice")
       body = (Var "sng")
       
test_3 :: Expr
test_3 =  Let "f" (App (Abs "x" (Var "x")) (Const $ Lit $ Literals.int32 0)) (Var "f")
 where sng0 = App (Var "sng") (Const $ Lit $ Literals.int32 0)
       sngAlice = App (Var "sng") (Const $ Lit $ Literals.string "alice")

test_4 :: Expr
test_4 = Let "sng" (Abs "x" (App (App (Const Cons) (Var "x")) (Const Nil))) body 
 where 
       body = (Var "sng")

test_5 :: Expr
test_5 = Let "sng" (Abs "x" (App (App (Const Cons) (Var "x")) (Const Nil))) body 
 where sng0 = App (Var "sng") (Const $ Lit $ Literals.int32 0)
       sngAlice = App (Var "sng") (Const $ Lit $ Literals.string "alice")
       body = App (App (Const Pair) sng0) sngAlice 

test_6 :: Expr
test_6 = letrec' "+" (Abs "x" $ Abs "y" $ recCall) twoPlusOne
 where
   recCall = App constSucc $ App (App (Var "+") (App constPred (Var "x"))) (Var "y")
   ifz x y z = App (App (App (Const If0) x) y) z
   twoPlusOne = App (App (Var "+") two) one
   two = App constSucc one
   one = App constSucc (Const $ Lit $ Literals.int32 0)

test_7 :: Expr
test_7 = letrec' "+" (Abs "x" $ Abs "y" $ recCall) $ twoPlusOne 
 where
   recCall = App constPred $ App (App (Var "+") (App constPred (Var "x"))) ( (Var "y"))
   ifz x y z = App (App (App (Const If0) x) y) z
   twoPlusOne = App (App (Var "+") two) one 
   two = App constPred one
   one = App constPred (Const $ Lit $ Literals.int32 0)

test_8 :: Expr
test_8 = letrec' "f" f x 
 where x =  (Var "f")
       f = Abs "x" $ Abs "y" $ App (App (Var "f") (Const $ Lit $ Literals.int32 0)) (Var "x")

test_9 :: Expr
test_9 = Letrec [("f", f), ("g", g)] x 
 where x =  App (App (Const $ Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "f") (Const $ Lit $ Literals.int32 0)) (Var "x")
       g = Abs "xx" $ Abs "yy" $ App (App (Var "g") (Const $ Lit $ Literals.int32 0)) (Var "xx")

test_10 :: Expr
test_10 = Letrec [("f", f), ("g", g)] b
 where b = App (App (Const Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (Const $ Lit $ Literals.int32 0)) (Var "x")
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (Var "v")) (Const $ Lit $ Literals.int32 0)

test_11 :: Expr
test_11 = Letrec [("f", f), ("g", g)] b
 where b = App (App (Const Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (Const $ Lit $ Literals.int32 0)) (Const $ Lit $ Literals.int32 0)
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (Var "v")) (Const $ Lit $ Literals.int32 0)

test_12 :: Expr
test_12 = Letrec [("f", f), ("g", g)] b
 where b = App (App (Const Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (Const $ Lit $ Literals.int32 0)) (Var "x")
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (Const $ Lit $ Literals.int32 0)) (Const $ Lit $ Literals.int32 0)
