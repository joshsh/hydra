{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}

-- Implementation of Hindley Milner algorithm W
-- to system F translation by Ryan Wisnesky, with extensions for Hydra by Joshua Shinavier
-- License: Apache 2.0 https://www.apache.org/licenses/LICENSE-2.0

module Hydra.AlgorithmW where

import Hydra.Minimal

import Prelude
import Control.Monad.Error
import Control.Monad.State
import Data.List (nub)
import Debug.Trace


natType = TyLit $ LiteralTypeInteger IntegerTypeInt32
constNeg = Const $ TypedPrim $ TypedPrimitive (Name "hydra/lib/math.neg") $ Forall [] $ TyFn natType natType
-- Note: Hydra has no built-in pred or succ functions, but neg has the expected type
constPred = constNeg
constSucc = constNeg
nat = Const . Lit . int32
str = Const . Lit . string

-- A typed primitive corresponds to the Hydra primitive of the same name
data TypedPrimitive = TypedPrimitive Name TypSch deriving (Eq)


------------------------
-- STLC

type Var = String

data Prim
 = Lit Literal
 | TypedPrim TypedPrimitive
 | If0
 | Fst | Snd | Pair | TT
 | Nil | Cons | FoldList
 | FF | Inl | Inr | Case | Con Var | Fold Var
 deriving Eq

instance Show Prim where
  show (Lit l) = show l
  show (TypedPrim (TypedPrimitive name _)) = unName name ++ "()"
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
  show (Con  n) = n
  show (Fold n) = "fold_" ++ n

data Expr = Const Prim
 | Var Var
 | Tuple [Expr]
 | Proj Int Int Expr
 | Inj Int Int Expr
 | Case' Expr [Expr]
 | App Expr Expr
 | Abs Var Expr
 | Letrec [(Var, Expr)] Expr
 deriving (Eq)

instance Show Expr where
  show (Case' t ts) = "case " ++ show t ++ " of " ++ x ++ " end"
   where x = foldl (\p q -> p ++ "\n\t\t" ++ q) "" $ map show ts
  show (Proj i j e) = show e ++ "." ++ show i ++ " (arity " ++ show j ++ ")"
  show (Inj i j e) = "inj " ++ show i ++ " (arity " ++ show j ++ ") " ++ show e
  show (Tuple ts) = "<" ++ show (map show ts) ++ ">"
  show (Const p) = show p
  show (Var v) = v
  show (App (App (App a' a) b) b') = "(" ++ show a' ++ " " ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (App (App a b) b') = "(" ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (Abs a b) = "(\\" ++ a ++ ". " ++ show b ++ ")"
  show (Letrec ab c) = "letrec " ++ d ++ show c
    where d = foldr (\(p, q) r -> p ++ " = " ++ show q ++ " \n\t\t" ++ r) "in " ab

data MTy = TyVar Var
  | TyLit LiteralType
  | TyList MTy
  | TyFn MTy MTy
  | TyProd MTy MTy
  | TySum MTy MTy
  | TyUnit
  | TyVoid
  | TyTuple [MTy]
  | TyVariant [MTy]
  | TyCon Var [MTy]
 deriving (Eq)

instance Show MTy where
  show (TyLit lt) = case lt of
    LiteralTypeInteger it -> drop (length "IntegerType") $ show it
    LiteralTypeFloat ft -> drop (length "FloatType") $ show ft
    _ -> drop (length "LiteralType") $ show lt
  show (TyTuple ts) = "(Tuple " ++ show (map show ts) ++ ")"
  show (TyVariant ts) = "(Variant " ++ show (map show ts) ++ ")"
  show (TyVar v) = v
  show (TyList t) = "(List " ++ (show t) ++ ")"
  show (TyFn t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TyProd t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++  ")"
  show (TySum t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++  ")"
  show TyUnit = "Unit"
  show TyVoid = "Void"
  show (TyCon c ts) = c ++ " " ++ ts'
   where ts' = foldr (\p r -> show p ++ "" ++ r) "" ts

instance Show TypSch where
  show (Forall [] t) = show t
  show (Forall x t) = "forall " ++ d ++ show t
   where d = foldr (\p q ->  p ++ " " ++ q) ", " x

data TypSch = Forall [Var] MTy
 deriving Eq


type ADTs = [(Var, [Var], [(Var, [MTy])])]




------------------------
-- System F

data FExpr = FConst Prim
 | FVar Var
 | FTuple [FExpr]
 | FProj Int FExpr
 | FInj Int [FTy] FExpr
 | FCase FExpr FTy [FExpr]
 | FApp FExpr FExpr
 | FAbs Var FTy FExpr
 | FTyApp FExpr [FTy]
 | FTyAbs [Var] FExpr
 | FLetrec [(Var, FTy, FExpr)] FExpr
 deriving (Eq)

instance Show FExpr where
  show (FCase t t' []) = "ff " ++ show t ++ " " ++ show t' ++ " "
  show (FCase t t' ts) = "case " ++ show t ++ " of " ++ show (map show ts) ++ " end"
  show (FProj i e) = show e ++ "." ++ show i
  show (FInj i j e) = "inj " ++ show i ++ " (arity " ++ show j ++ ") " ++ show e
  show (FTuple es) = "<" ++ show (map show es) ++ ">"
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

data FTy = FTyVar Var
  | FTyLit LiteralType
  | FTyList FTy
  | FTyFn FTy FTy
  | FTyProd FTy FTy
  | FTySum FTy FTy
  | FTyUnit
  | FTyVoid
  | FTyTuple [FTy]
  | FTyVariant [FTy]
  | FTyCon Var [FTy]
  | FForall [Var] FTy
 deriving (Eq)

instance Show FTy where
  show (FTyLit lt) = show $ TyLit lt
  show (FTyVariant ts) = "(Variant " ++ show (map show ts) ++ ")"
  show (FTyTuple ts) = "(Tuple " ++ show (map show ts) ++ ")"
  show (FTyVar v) = v
  show (FTyList t) = "(List " ++ (show t) ++ ")"
  show (FTyFn t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (FTyProd t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++  ")"
  show (FTySum t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++  ")"
  show FTyUnit = "Unit"
  show FTyVoid = "Void"
  show (FForall x t) = "(forall " ++ d ++ show t ++ ")"
   where d = foldr (\p q -> p ++ " " ++ q) ", " x
  show (FTyCon c ts) = c ++ " " ++ ts'
   where ts' = foldr (\p r -> show p ++ "" ++ r) " " ts

mTyToFTy :: MTy -> FTy
mTyToFTy (TyVar v) = FTyVar v
mTyToFTy (TyLit lt) = FTyLit lt
mTyToFTy TyUnit = FTyUnit
mTyToFTy TyVoid = FTyVoid
mTyToFTy (TyList x) = FTyList $ mTyToFTy x
mTyToFTy (TyFn x y) = FTyFn (mTyToFTy x) (mTyToFTy y)
mTyToFTy (TyProd x y) = FTyProd (mTyToFTy x) (mTyToFTy y)
mTyToFTy (TySum x y) = FTySum (mTyToFTy x) (mTyToFTy y)
mTyToFTy (TyTuple ts) = FTyTuple (map mTyToFTy ts)
mTyToFTy (TyVariant ts) = FTyVariant (map mTyToFTy ts)
mTyToFTy (TyCon c ts) = FTyCon c $ map mTyToFTy ts

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
 vars (TyLit _) = []
 vars (TyList t) = vars t
 vars (TyFn t1 t2) = vars t1 ++ vars t2
 vars TyUnit = []
 vars TyVoid = []
 vars (TyProd t1 t2) = vars t1 ++ vars t2
 vars (TySum t1 t2) = vars t1 ++ vars t2
 vars (TyTuple []) = []
 vars (TyTuple (a:b)) = vars a ++ vars (TyTuple b)
 vars (TyVariant []) = []
 vars (TyVariant (a:b)) = vars a ++ vars (TyVariant b)
 vars (TyCon _ x) = vars $ TyVariant x --cheat

replaceTCon :: MTy -> MTy -> MTy -> MTy
replaceTCon u s (TyVar x) = TyVar x
replaceTCon u s (TyLit l) = TyLit l
replaceTCon u s (TyList t)  = TyList $ replaceTCon u s t
replaceTCon u s (TyFn t1 t2)  = TyFn (replaceTCon u s t1) (replaceTCon u s t2)
replaceTCon u s TyUnit  = TyUnit
replaceTCon u s TyVoid  = TyVoid
replaceTCon u s (TyProd t1 t2)  = TyProd (replaceTCon u s t1) (replaceTCon u s t2)
replaceTCon u s (TySum t1 t2)  = TySum (replaceTCon u s t1) (replaceTCon u s t2)
replaceTCon u s (TyTuple [])  = TyTuple []
replaceTCon u s (TyTuple (a:b)) = TyTuple $ (replaceTCon u s a):(map (replaceTCon u s) b)
replaceTCon u s (TyVariant [])  = TyVariant []
replaceTCon u s (TyVariant (a:b)) = TyVariant $ (replaceTCon u s a):(map (replaceTCon u s) b)
replaceTCon u s (TyCon t' ts)  | TyCon t' ts == u = s
                               | otherwise = TyCon t' $ map (replaceTCon u s) ts

primTy :: ADTs -> Prim -> Either String TypSch
primTy _ (Lit l) = Right $ Forall [] $ TyLit $ literalType l
primTy _ (TypedPrim (TypedPrimitive _ forall)) = Right forall
primTy [] (Con n) = throwError $ n ++ " not found "
primTy ((a,t,[]):tl) (Con n) = primTy tl $ Con n
primTy ((a,t,(c,ts):cs):tl) (Con n) | c == n = return $ Forall t (ts' ts $ TyCon a $ map TyVar t)
                                    | otherwise = primTy ((a,t,cs):tl) $ Con n
 where ts' [] x = x
       ts' (p:q) x = TyFn p $ ts' q x
primTy [] (Fold n) = throwError $ n ++ " not found "
primTy ((a,t,cs):tl) (Fold n) | a == n = return $ Forall ("r":t) $ elimTy
                              | otherwise = primTy tl $ Fold n
 where elimTy = TyFn (TyCon a $ map TyVar t) $ replaceTCon (TyCon a $ map TyVar t) (TyVar "r") (ts' cs)
       ts' [] = TyVar "r"
       ts' ((_,ts):q)  = TyFn (ts'' ts) $ ts' q
       ts'' [] = TyCon a $ map TyVar t
       ts'' (a:b) = TyFn a $ ts'' b
primTy _ Fst = return $  Forall ["x", "y"] $ (TyProd (TyVar "x") (TyVar "y")) `TyFn` (TyVar "x")
primTy _ Snd = return $  Forall ["x", "y"] $ (TyProd (TyVar "x") (TyVar "y")) `TyFn` (TyVar "y")
primTy _ Nil = return $  Forall ["t"] $ TyList (TyVar "t")
primTy _ Cons = return $ Forall ["t"] $ TyFn (TyVar "t") (TyFn (TyList (TyVar "t")) (TyList (TyVar "t")))
primTy _ TT = return $ Forall [] TyUnit
primTy _ FF = return $ Forall ["t"] $ TyFn TyVoid (TyVar "t")
primTy _ Inl = return $ Forall ["x", "y"] $ (TyVar "x") `TyFn` (TyProd (TyVar "x") (TyVar "y"))
primTy _ Inr = return $ Forall ["x", "y"] $ (TyVar "y") `TyFn` (TyProd (TyVar "x") (TyVar "y"))
primTy _ Pair = return $ Forall ["xx", "yy"] $ (TyFn (TyVar "xx") (TyFn (TyVar "yy") (TyProd (TyVar "xx") (TyVar "yy"))))
primTy _ If0 = return $ Forall [] $ natType `TyFn` (natType `TyFn` (natType `TyFn` natType))
primTy _ FoldList = return $ Forall ["a", "b"] $ p `TyFn` ((TyVar "b") `TyFn` ((TyList $ TyVar "a") `TyFn` (TyVar "b")))
 where p = TyVar "b" `TyFn` (TyVar "a" `TyFn` TyVar "b")
primTy _ Case = return $ Forall ["x", "y", "z"] $ (TySum (TyVar "x") (TyVar "y")) `TyFn` (l `TyFn` (r `TyFn` (TyVar "z")))
 where l = (TyVar "x") `TyFn` (TyVar "z")
       r = (TyVar "y") `TyFn` (TyVar "z")


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

class Substable a where
  subst :: Subst -> a -> a

instance Substable MTy where
 subst f (TyLit lt) = TyLit lt
 subst f (TyVariant ts) = TyVariant $ map (subst f) ts
 subst f (TyTuple ts) = TyTuple $ map (subst f) ts
 subst f TyUnit = TyUnit
 subst f TyVoid = TyVoid
 subst f (TyList t) = TyList $ subst f t
 subst f (TyFn t1 t2) = TyFn (subst f t1) (subst f t2)
 subst f (TyProd t1 t2) = TyProd  (subst f t1) (subst f t2)
 subst f (TySum t1 t2) = TySum  (subst f t1) (subst f t2)
 subst f (TyVar v) = case lookup v f of
                      Nothing -> TyVar v
                      Just y -> y
 subst f (TyCon v ts) = TyCon v $ map (subst f) ts

instance Substable FTy where
 subst f (FTyLit lt) = FTyLit lt
 subst f (FTyVariant ts) = FTyVariant $ map (subst f) ts
 subst f (FTyTuple ts) = FTyTuple $ map (subst f) ts
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
 subst f (FTyCon v ts) = FTyCon v $ map (subst f) ts

instance Substable TypSch where
 subst f (Forall vs t) = Forall vs $ subst f' t
   where f' = filter (\(v,t')-> not $ elem v vs) f

instance Substable Ctx where
 subst phi g = map (\(k,v)->(k, subst phi v)) g

instance Substable FExpr where
 subst phi (FInj i js e) = FInj i (map (subst phi) js) $ subst phi e
 subst phi (FProj i e) = FProj i $ subst phi e
 subst phi (FTuple es) = FTuple $ map (subst phi) es
 subst phi (FCase e t es) = FCase (subst phi e) (subst phi t) $ map (subst phi) es
 subst phi (FConst p) = FConst p
 subst phi (FVar p) = FVar p
 subst phi (FApp p q) = FApp (subst phi p) (subst phi q)
 subst phi (FAbs p t q) = FAbs p (subst phi t) (subst phi q)
 subst phi (FTyApp p q) = FTyApp (subst phi p) (map (subst phi) q)
 subst phi (FTyAbs vs p) = FTyAbs vs (subst phi' p)
  where phi' = filter (\(v,f')-> not (elem v vs)) phi
 subst phi (FLetrec vs p) = FLetrec (map (\(k,t,v)->(k,subst phi t, subst phi v)) vs) (subst phi p)

subst' :: [(Var,FTy)] -> FTy -> FTy
subst' f (FTyLit lt) = FTyLit lt
subst' f (FTyTuple ts) = FTyTuple $ (map $ subst' f) ts
subst' f (FTyVariant ts) = FTyVariant $ (map $ subst' f) ts
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
subst' f (FTyCon v ts) = FTyCon v $ map (subst' f) ts

instance Show Ctx where
  show [] = ""
  show ((k,v):t) = k ++ ":" ++ show v ++ " " ++ show t

------------------------------------
-- Type checking for F

open :: [Var] -> [FTy] -> FTy -> Either String FTy
open vs ts e | length vs == length ts = return $ subst' (zip vs ts) e
             | otherwise = throwError "Cannot open"

typeOf :: ADTs -> [Var] -> [(Var,FTy)] -> FExpr -> Either String FTy
typeOf adts tvs g (FCase e r es) = do { ts <- mapM (typeOf adts tvs g) es
                                      ; t <- typeOf adts tvs g e
                                      ; case t of
                                         FTyVariant ts' -> if length ts == length ts'
                                                           then do { mapM f $ zip ts ts'
                                                                   ; return r }
                                                           else throwError $ "bad number of cases "
                                         z -> throwError $ show z ++ " is not a variant"}
 where f ((FTyFn a b), exp) | a == exp && b == r = return ()
typeOf adts tvs g (FInj i ts e) = do { t <- typeOf adts tvs g e
                                     ; if i >= length ts
                                       then throwError $ "bad inj index " ++ show i ++ " on " ++ show e
                                       else if ts !! i == t
                                            then return $ FTyVariant ts
                                            else throwError $ "injection type mismatch " ++ show (FInj i ts e) ++ ", " ++ show (ts !! i) ++ " <> " ++ show t }
typeOf adts tvs g (FProj i e) = do { t <- typeOf adts tvs g e
                                   ; case t of
                                      FTyTuple ts -> if i >= length ts
                                                     then throwError $ "bad proj index " ++ show i ++ " on " ++ show e
                                                     else return $ ts !! i
                                      z -> throwError $ show z ++ " is not a tuple type" }
typeOf adts tvs g (FTuple es) = do { ts <- mapM (typeOf adts tvs g) es
                                   ; return $ FTyTuple ts }
typeOf adts tvs g (FVar x) = case lookup x g of
  Nothing -> throwError $ "unbound var: " ++ x
  Just y -> return y
typeOf adts tvs g (FConst p) = do { t <- primTy adts p ; return $ tyToFTy t }
typeOf adts tvs g (FApp a b) = do { t1 <- typeOf adts tvs g a
                                  ; t2 <- typeOf adts tvs g b
                                  ; case t1 of
                                      FTyFn p q -> if p == t2
                                                   then return q
                                                   else throwError $ "In " ++ (show $ FApp a b) ++ " expected " ++ show p ++ " given " ++ show t2
                                      v -> throwError $ "In " ++ show (FApp a b) ++ " not a fn type: " ++ show v }
typeOf adts tvs g (FAbs x t e) = do { t1 <- typeOf adts tvs ((x,t):g) e
                                    ; return $ t `FTyFn` t1 }
typeOf adts tvs g (FTyAbs vs e) = do { t1 <- typeOf adts (vs++tvs) g e
                                     ; return $ FForall vs t1 }
typeOf adts tvs g (FTyApp e ts) = do { t1 <- typeOf adts tvs g e
                                     ; case t1 of
                                        FForall vs t -> open vs ts t
                                        v -> throwError $ "not a forall type: " ++ show v }
typeOf adts tvs g (FLetrec es e) = do { let g' = map (\(k,t,e)->(k,t)) es
                                      ; est <- mapM (\(_,_,v)->typeOf adts tvs (g'++g) v) es
                                      ; if est == (snd $ unzip g')
                                        then typeOf adts tvs g' e
                                        else throwError $ "Disagree: " ++ show est ++ " and " ++ (show $ snd $ unzip g') }


-----------------------------
-- Unification

mgu :: MTy -> MTy -> E Subst
mgu (TyLit lt1) (TyLit lt2) = if lt1 == lt2
  then return []
  else throwError $ "Cannot unify literal types " ++ show lt1 ++ " and " ++ show lt2
mgu (TyVariant ts1) (TyVariant ts2) | length ts1 == length ts2 = mgu' ts1 ts2
                                    | otherwise = throwError $ "cannot unify " ++ show ts1 ++ " with " ++ show ts2
mgu (TyTuple ts1) (TyTuple ts2) | length ts1 == length ts2 = mgu' ts1 ts2
                                | otherwise = throwError $ "cannot unify " ++ show ts1 ++ " with " ++ show ts2
mgu (TyList a) (TyList b) = mgu a b
mgu TyUnit TyUnit = return []
mgu TyVoid TyVoid = return []
mgu (TyCon a as) (TyCon b bs) | a == b && length as == length bs = mgu' as bs
                              | otherwise = throwError $ "cannot unify " ++ show a ++ " with " ++ show b
mgu (TyProd a b) (TyProd a' b') = do { s <- mgu a a' ; s' <- mgu (subst s b) (subst s b'); return $ s' `o` s }
mgu (TySum  a b) (TySum  a' b') = do { s <- mgu a a' ; s' <- mgu (subst s b) (subst s b'); return $ s' `o` s }
mgu (TyFn   a b) (TyFn   a' b') = do { s <- mgu a a' ; s' <- mgu (subst s b) (subst s b'); return $ s' `o` s }
mgu (TyVar a) (TyVar b) | a == b = return []
mgu (TyVar a) b = do { occurs a b; return [(a, b)] }
mgu a (TyVar b) = mgu (TyVar b) a
mgu a b = throwError $ "cannot unify " ++ show a ++ " with " ++ show b

mgu' :: [MTy] -> [MTy] -> E Subst
mgu' [] [] = return idSubst
mgu' (a:as) (b:bs) = do { f <- mgu a b; s <- mgu' (map (subst f) as) (map (subst f) bs); return $ s `o` f }

occurs :: Var -> MTy -> E ()
occurs v (TyLit _) = return ()
occurs v (TyCon _ ts) = mapM_ (occurs v) ts
occurs v (TyTuple ts) = mapM_ (occurs v) ts
occurs v (TyVariant ts) = mapM_ (occurs v) ts
occurs v (TyList l) = occurs v l
occurs v TyUnit = return ()
occurs v TyVoid = return ()
occurs v (TyFn   a b) = do { occurs v a; occurs v b }
occurs v (TyProd a b) = do { occurs v a; occurs v b }
occurs v (TySum  a b) = do { occurs v a; occurs v b }
occurs v (TyVar v') | v == v' = throwError $ "occurs check failed"
                    | otherwise = return ()

-----------------------------
-- Algorithm W

type E = ErrorT String (State ([String],Integer))
type M a = E (Subst, a)

log0 :: Int -> String -> E ()
log0 i x = do { (l, s) <- get; put ((x'++x):l, s); }
 where x' = foldl (\p q -> "\t" ++ p) "" [0..i]

fresh :: E MTy
fresh = do { (l,s) <- get; put (l, s + 1); return $ TyVar $ "v" ++ show s }

inst :: TypSch -> E (MTy,[MTy])
inst (Forall vs ty) = do { vs' <- mapM (\_->fresh) vs; return $ (subst (zip vs vs') ty,  vs') }

gen :: Ctx -> MTy -> (TypSch, [Var])
gen g t = (Forall vs t , vs)
 where vs = nub $ filter (\v -> not $ elem v (vars g)) (vars t)

fTyApp x [] = x
fTyApp x y = FTyApp x y

fTyAbs [] x = x
fTyAbs x y = FTyAbs x y

replace [] _ = []
replace (_:xs) (0,a) = a:xs
replace (x:xs) (n,a) =
  if n < 0
    then (x:xs)
    else x: replace xs (n-1,a)

checkAgainstF :: ADTs -> Ctx -> MTy -> FExpr -> E ()
checkAgainstF adts g t e = case (typeOf adts [] g' e) of
                              Left err -> throwError  $ "\t" ++  "err: " ++ err
                              Right tt -> if tt == mTyToFTy t
                                          then return ()
                                          else throwError $ show g ++ "|- " ++ show e ++ ": " ++ show tt ++ " != " ++ show t
 where g' = map (\(k,v)->(k, tyToFTy v)) g

w :: Int -> ADTs -> Ctx -> Expr -> M (MTy, FExpr)
w l adts g (Case' e es') = do { t <- fresh
                            ; bs' <- mapM (\_->fresh) es'
                            ; let bs = map (\k-> TyFn k t) bs'
                            ; (phi , (ts, es)) <- w' (l+1) g es'
                            ; m1 <- mgu' bs ts
                            ; (phi', (t', e')) <- w  (l+1) adts (subst (m1 `o` phi) g) e
                            ; m2 <- mgu (subst (m1 `o` phi) t') (subst (m1 `o` phi' `o` phi) $ TyVariant bs')
                            ; let ret = FCase (subst (m2 ) e') (mTyToFTy ret_t) (map (subst $ m2 `o` phi' `o` m1) es)
                                  ret_t = subst ret_subst t
                                  ret_subst = m2 `o` phi' `o` m1 `o` phi
                            ; checkAgainstF adts (subst ret_subst g) ret_t ret
                            ; return (ret_subst, (ret_t, ret)) }
 where w' l g [] = return (idSubst, ([], []))
       w' l g (e:tl) = do { (u,(u', j)) <- w l adts g e
                        ; (r,(r', h)) <- w' l (subst u g ) tl
                        ; return (r `o` u, ((subst r u'):r', (subst r j):h)) }
w l adts g (Inj i j e) = do {
                     ; (s0, (t0, a)) <- w (l+1) adts g e
                     ; t'' <- mapM (\_->fresh) [1..j]
                     ; let t' = replace t'' (i, t0)
                     ; let ret = FInj i (map (mTyToFTy) t') a
                           ret_t = TyVariant t'
                           ret_subst = s0
                     ; log0 l $ "INJ " ++ show (subst ret_subst g) ++ "|- " ++ (show $ ret) ++ " : " ++  show ret_t
                     ; checkAgainstF adts (subst ret_subst g) ret_t ret
                     ; return (ret_subst, (ret_t, ret)) }
w l adts g (Proj i j e) = do {
                     ; (s0, (t0, a)) <- w (l+1) adts g e
                     ; t' <- mapM (\_->fresh) [1..j]
                     ; s2 <-  t0 `mgu` (TyTuple t')
                     ; let ret = FProj i (subst s2 a)
                           ret_t = subst s2 (t' !! i)
                           ret_subst = s2 `o` s0
                     ; log0 l $ "PROJ " ++ show (subst ret_subst g) ++ "|- " ++ (show $ ret) ++ " : " ++  show ret_t
                     ; checkAgainstF adts (subst ret_subst g) ret_t ret
                     ; return (ret_subst, (ret_t, ret)) }
w l adts g (Tuple es') = do { (phi, (ts, es)) <- w' (l+1) g es'
                            ; let ret = FTuple es
                                  ret_t = TyTuple ts
                                  ret_subst = phi
                            ; log0 l $ "TUPLE " ++ show (subst ret_subst g) ++ "|- " ++ (show $ ret) ++ " : " ++  show ret_t
                            ; checkAgainstF adts (subst ret_subst g) ret_t ret
                            ; return (ret_subst, (ret_t, ret)) }
 where w' l g [] = return (idSubst, ([], []))
       w' l g (e:tl) = do { (u,(u', j)) <- w l adts g e
                        ; (r,(r', h)) <- w' l (subst u g ) tl
                        ; return (r `o` u, ((subst r u'):r', (subst r j):h)) }
w l adts g (Const p) = do { case primTy adts p of
                              Left er -> throwError er
                              Right t -> do { (ret_t, vs) <- inst t
                        ; let ret = fTyApp (FConst p) $ map mTyToFTy vs
                          ; log0 l $ "CONST " ++ show g ++ "|- " ++  show ret ++ " : " ++ show ret_t
                        ; checkAgainstF adts g ret_t ret
                        ; return (idSubst, (ret_t, ret)) } }
w l adts g (Var x) = case lookup x g of
                Nothing -> throwError $ "Unknown var: " ++ (show x)
                Just s -> do { (ret_t, vs) <- inst s
                             ; let ret = fTyApp (FVar x) $ map mTyToFTy vs
                             ; log0 l $ "VAR " ++ show g ++ "|- " ++ show ret ++ " : " ++ show ret_t
                             ; checkAgainstF adts g ret_t ret
                             ; return (idSubst, (ret_t, ret)) }
w l adts g (App e0 e1) = do {
                     ; (s0, (t0, a)) <- w (l+1) adts g e0
                     ; (s1, (t1, b)) <- w (l+1) adts (subst s0 g) e1
                     ; t' <- fresh
                     ; s2 <-  (subst s1 t0) `mgu` (t1 `TyFn` t')
                     ; let ret = FApp (subst (s2 `o` s1) a) (subst s2 b)
                           ret_t = subst s2 t'
                           ret_subst = s2 `o` (s1 `o` s0);
                     ; log0 l $ "APP " ++ show (subst ret_subst g) ++ "|- " ++ show ret ++ " : " ++  show ret_t
                     ; checkAgainstF adts (subst ret_subst g) ret_t ret
                     ; return (ret_subst, (ret_t, ret)) }
w l adts g (Abs x e) = do {
                        ; t  <- fresh
                        ; (ret_subst, (t', a)) <- w (l+1) adts ((x, (Forall [] t)):g) e
                        ; let ret = FAbs x (mTyToFTy $ subst ret_subst t) a
                              ret_t = TyFn (subst ret_subst t) t'
                        ; log0 l $ "ABS " ++ show (subst ret_subst g) ++ "|- \\" ++ x ++ ". " ++ show ret ++ " : " ++ show ret_t
                        ; checkAgainstF adts (subst ret_subst g) ret_t ret
                        ; return (ret_subst, (ret_t, ret)) }
w l adts g (Letrec xe0 e1) = do {
                         ; t0s <- mapM (\(k,v) -> do { f <- fresh; return (k, f) }) xe0
                         ; let g' = map (\(k,v) -> (k, Forall [] v)) t0s ++ g
                         ; (s0, (ts,e0XS)) <- w' (l+1) g' xe0
                         ; s' <- mgu' (map (\(_,v) -> subst s0 v) t0s) ts
                         ; let g'' = subst (s' `o` s0) g'
                               g'''  = map (\(k,t) -> (k, fst $ gen g (subst s' t))) $ zip (fst $ unzip xe0) ts
                         ; (s1, (t',e1X)) <- w (l+1) adts (g''') e1
                         ; let g''X = map (\(k,t) -> (k, gen g (subst (s') t))) $ zip (fst $ unzip xe0) ts
                               e0Xs = map (subst (s1 `o` s')) e0XS
                               mmm = map (\((x,(ww,ww2)),e0X)->(x, (fTyApp (FVar x) $ map FTyVar ww2))) $  zip g''X e0Xs
                               e0X's =  map (\((x,(ww,ww2)),e0X)->(x,ww,ww2, subst'' mmm e0X)) $ zip g''X e0Xs
                               e0X''s = map (\(x,ww,ww2,e) -> (x,ww,ww2,fTyAbs ww2 e)) e0X's
                               bs = map (\(x,ww,ww2,e0X'') -> (x, subst s1 $ tyToFTy ww, subst (s' `o` s1) e0X'')) e0X''s
                               ret = FLetrec bs e1X
                               ret_t = t'
                               ret_subst = s1 `o` s' `o` s0
                        ; log0 l $ "LETREC " ++ show (subst ret_subst g) ++ "|- " ++ show ret ++ " : " ++ show ret_t
                        ; checkAgainstF adts (subst ret_subst g) ret_t ret
                        ; return (ret_subst, (ret_t, ret)) }
 where w' l g [] = return (idSubst, ([], []))
       w' l g  ((k,v):tl) = do { (u,(u', j)) <- w l adts g v
                             ; (r,(r', h)) <- w' l (subst u g ) tl
                             ; return (r `o` u, ((subst r u'):r', (subst r j):h)) }


subst'' :: [(Var, FExpr)] -> FExpr -> FExpr
subst'' phi (FTuple es) = FTuple $ map (subst'' phi) es
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

----------------------------------------
-- Main

theAdts = theAdtsJosh ++ [("List", ["t"], [("Nil", []), ("Cons", [TyVar "t", TyCon "List" [TyVar "t"]])])]

theAdtsJosh = [("LatLon1", [], [("MkLatLon1", [natType, natType])]),
               ("LatLon2", [], [("MkLatLon2", [natType, natType])])]
{--  data LatLon1 = MkLatOn1 Nat Nat where lat1 (MkLatLon1 a) = a and lon1 (MkLatLon1 b) = b and also data LatLon2 = MkLatOn2 Nat Nat where lat2 (MkLatLon2 a ) = a and lon2 (MkLatLon2  b) = --}

testJoshAdt = Letrec [("lat1", lat1)] body
 where body = App (App (Const $ Con "MkLatLon1") (nat 0)) (nat 1)
       lat1 = Abs "z" $ App (App (Const $ Fold "LatLon1") (Var "z")) $ Abs "p" $ Abs "q" $ (Var "p")

testJoshAdt' = Letrec [("lat1", lat1)] $ App (Var "lat1") body
 where body = App (App (Const $ Con "MkLatLon1") (nat 0)) (nat 1)
       lat1 = Abs "z" $ App (App (Const $ Fold "LatLon1") (Var "z")) $ Abs "p" $ Abs "q" $ (Var "p")

tests = [testJoshAdt, testJoshAdt'] -- testVariant2, testTuple2, testVariant, testTuple, test_j_0, test_j_0' , testJ,  test4, testk, testC, testA, test0, test1, testB, test2, test3a, test5, test6]

testk = Letrec [("f", f), ("g", g)] b
 where b = Tuple [(Var "f"), (Var "g")]
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (nat 0)) (Var "x")
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (Var "v")) (nat 0)

testJ = letrec' "f" i b
 where i = Abs "x" (Var "x")
       b = Var "f"

testAdt = Abs "z" $ App (App (App (Const $ Fold "List") $ Var "z") (Const $ Con "Nil")) (Const $ Con "Cons")

testOne t = do { putStrLn $ "Untyped input: "
               ; putStrLn $ "\t" ++  show t
               ; let out = runState (runErrorT (w 0 theAdts [] t)) ([],0)
               ; case fst out of
                   Left  e -> do { putStrLn $ "\t" ++ "err: " ++ e
                                 ; putStrLn $ "\nLog:"
                                 ; mapM_ (putStrLn) $ reverse $ fst $ snd out }
                   Right (s, (ty, f)) -> do { putStrLn $ "\nType inferred by Hindley-Milner: "
                                            ; putStrLn $ "\t" ++ show ty
                                            ; putStrLn "\nSystem F translation: "
                                            ; putStrLn $ "\t" ++ show f
                                            -- ; putStrLn "\nLog: "
                                            -- ; mapM_ (putStrLn) $ reverse $ fst $ snd out
                                            }
               ; putStrLn ""
               ; putStrLn "------------------------"
               ; putStrLn ""  }

main = mapM testOne tests

letrec' x e f = Letrec [(x,e)] f

testVariant :: Expr
testVariant = Abs "z" $ Case' (Var "z") [f,g]
 where f = Abs "x" {-- $ Inj 0 2 --} $ Var "x"
       g = Abs "y" {-- $ Inj 1 2 --} $ Var "y"
      -- t = Variant [f, g]

testVariant2 :: Expr
testVariant2 = Abs "z" $ Case' (Var "z") [f,g]
 where f = Abs "x" $ Inj 0 2 $ Var "x"
       g = Abs "y" $ Inj 1 2 $ Var "y"
      -- t = Variant [f, g]

testTuple2 :: Expr
testTuple2 = Abs "z" $ Tuple [(Proj 0 2 $ Var "z"), (Proj 1 2 $ Var "z")]

testTuple :: Expr
testTuple = Letrec [("t", t)] $ Tuple [Proj 1 2 $ Var "t", Proj 0 2 $ Var "t"]
 where f = str "alice"
       g = nat 0
       t = Tuple [f, g]


testA :: Expr
testA =  letrec' "f" ( (Abs "x" (Var "x"))) $ App (Var "f")  (nat 0)
 where sng0 = App (Var "sng") (nat 0)
       sngAlice = App (Var "sng") (str "alice")
       body = (Var "sng")

test0 :: Expr
test0 =  letrec' "f" (App (Abs "x" (Var "x")) (nat 0)) (Var "f")
 where sng0 = App (Var "sng") (nat 0)
       sngAlice = App (Var "sng") (str "alice")


testB :: Expr
testB = letrec' "sng" (Abs "x" (App (App (Const Cons) (Var "x")) (Const Nil))) body
 where
       body = (Var "sng")

test1 :: Expr
test1 = letrec' "sng" (Abs "x" (App (App (Const Cons) (Var "x")) (Const Nil))) body
 where sng0 = App (Var "sng") (nat 0)
       sngAlice = App (Var "sng") (str "alice")
       body = App (App (Const Pair) sng0) sngAlice

test2 :: Expr
test2 = letrec' "+" (Abs "x" $ Abs "y" $ recCall) twoPlusOne
 where
   recCall = App constSucc $ App (App (Var "+") (App constPred (Var "x"))) (Var "y")
   ifz x y z = App (App (App (Const If0) x) y) z
   twoPlusOne = App (App (Var "+") two) one
   two = App constSucc one
   one = App constSucc (nat 0)

testC :: Expr
testC = letrec' "+" (Abs "x" $ Abs "y" $ recCall) $ twoPlusOne
 where
   recCall = App constSucc $ App (App (Var "+") (App constPred (Var "x"))) ( (Var "y"))
   ifz x y z = App (App (App (Const If0) x) y) z
   twoPlusOne = App (App (Var "+") two) one
   two = App constSucc one
   one = App constSucc (nat 0)

test3 :: Expr
test3 = letrec' "f" f x
 where x =  (Var "f")
       f = Abs "x" $ Abs "y" $ App (App (Var "f") (nat 0)) (Var "x")

test3a :: Expr
test3a = Letrec [("f", f), ("g", g)] x
 where x =  App (App (Const $ Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "f") (nat 0)) (Var "x")
       g = Abs "xx" $ Abs "yy" $ App (App (Var "g") (nat 0)) (Var "xx")

test4 :: Expr
test4 = Letrec [("f", f), ("g", g)] b
 where b = App (App (Const Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (nat 0)) (Var "x")
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (Var "v")) (nat 0)

test5 :: Expr
test5 = Letrec [("f", f), ("g", g)] b
 where b = App (App (Const Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (nat 0)) (nat 0)
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (Var "v")) (nat 0)


test6 :: Expr
test6 = Letrec [("f", f), ("g", g)] b
 where b = App (App (Const Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (nat 0)) (Var "x")
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (nat 0)) (nat 0)


x @@ y = App x y
zero = nat 0

test_j_o_haskell = f
  where
    sng = \x -> [x]
    f = \x y -> (sng x, sng y): []
    g = \x y -> f 0 y

-- @joshsh's additional test cases
test_j_0 :: Expr
test_j_0 = Letrec [("singleton", singleton), ("f", f), ("g", g)] $ Var "f"
  where
    singleton = Abs "x" $ Const Cons @@ Var "x" @@ Const Nil
    f = Abs "x" $ Abs "y" $ Const Cons
      @@ (Const Pair
        @@ (Var "singleton" @@ Var "x")
        @@ (Var "singleton" @@ Var "y"))
      @@ (Var "g" @@ Var "x" @@ Var "y")
    g = Abs "x" $ Abs "y" $ Var "f" @@ zero @@ Var "y"

test_j_0' :: Expr
test_j_0' = Letrec [("singleton", singleton)] $
 Letrec [("f", f), ("g", g)] $ Var "f"
  where
    singleton = Abs "x" $ Const Cons @@ Var "x" @@ Const Nil
    f = Abs "x" $ Abs "y" $ Const Cons
      @@ (Const Pair
        @@ (Var "singleton" @@ Var "x")
        @@ (Var "singleton" @@ Var "y"))
      @@ (Var "g" @@ Var "x" @@ Var "y")
    g = Abs "x" $ Abs "y" $ Var "f" @@ zero @@ Var "y"

--test_j_0 :: Expr
--test_j_0 = Let "id" i $ f
  --where
   -- i = Abs "z" $ Var "z"
   -- f = Abs "p0" $
     --  (Const Pair)
       -- @@ (Var "id" @@ Var "p0")
       -- @@ (Var "p0")
