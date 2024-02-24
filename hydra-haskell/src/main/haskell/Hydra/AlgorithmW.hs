{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- Implementation of Hindley Milner algorithm W 
-- to system F translation by Ryan Wisnesky.
-- License: Apache 2.0 https://www.apache.org/licenses/LICENSE-2.0 

module Hydra.AlgorithmW where

import qualified Hydra.Core as Core

import Prelude
import Control.Monad.Error
import Control.Monad.State
import Data.List (nub)

import qualified Data.List as L
import qualified Data.Map as M
import qualified Control.Monad as CM

------------------------
-- STLC

type Var = String

data Prim = PrimStr String 
 | PrimNat Integer | Succ | Pred | If0 
 | Fst | Snd | Pair | TT
 | Nil | Cons | FoldList  
 | FF | Inl | Inr | Case 
 deriving Eq
 
instance Show Prim where
  show (PrimStr s) = s
  show (PrimNat i) = show i
  show Succ = "S" 
  show Pred = "P"
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
 | Letrec' Var Expr Expr --include separate impl of unary letrec 
 deriving (Eq)

instance Show Expr where 
  show (Const p) = show p
  show (Var v) = v
  show (App (App (App a' a) b) b') = "(" ++ show a' ++ " " ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (App (App a b) b') = "(" ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (Abs a b) = "(\\" ++ a ++ ". " ++ show b ++ ")"
  show (Let a b c) = "let " ++ a ++ " = " ++ show b ++ " in " ++ show c 
  show (Letrec' a b c) = "letrec " ++ a ++ " = " ++ show b ++ " in " ++ show c 
  show (Letrec ab c) = "letrecs " ++ d ++ show c 
    where d = foldr (\(p, q) r -> p ++ " = " ++ show q ++ " \n\t\t" ++ r) "in " ab

data MTy = TyVar Var 
  | TyNat 
  | TyString
  | TyList MTy 
  | TyFn MTy MTy
  | TyProd MTy MTy
  | TySum MTy MTy
  | TyUnit 
  | TyVoid
 deriving (Eq)
 
instance Show MTy where
  show TyNat = "Nat"
  show TyString = "String"
  show (TyVar v) = v
  show (TyList t) = "(List " ++ (show t) ++ ")"
  show (TyFn t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TyProd t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++  ")"
  show (TySum t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++  ")"
  show TyUnit = "Unit"
  show TyVoid = "Void"
  
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
 deriving (Eq)

instance Show FExpr where 
  show (FConst p) = show p
  show (FVar v) = v
  show (FTyApp e t) = "(" ++ show e ++ " : " ++ show t ++ ")"
  show (FApp (FApp (FApp a' a) b) b') = "(" ++ show a' ++ " " ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (FApp (FApp a b) b') = "(" ++ show a ++ " " ++ show b ++ " " ++ show b' ++ ")"
  show (FApp a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (FAbs a t b) = "(\\" ++ a ++ ":" ++ show t ++ ". " ++ show b ++ ")"
  show (FLetrec ab c) = "letrecs " ++ d ++ show c 
    where d = foldr (\(p, t, q) r -> p ++ ":" ++ show t ++ " = " ++ show q ++ " \n\t\t" ++ r) "in " ab
  show (FTyAbs ab c) = "(/\\" ++ d ++ show c ++ ")"
    where d = foldr (\p r -> p ++ " " ++ r) ". " ab

data FTy = FTyVar Var 
  | FTyNat 
  | FTyString
  | FTyList FTy 
  | FTyFn FTy FTy
  | FTyProd FTy FTy
  | FTySum FTy FTy
  | FTyUnit 
  | FTyVoid
  | FForall [Var] FTy
 deriving (Eq)
 
instance Show FTy where
  show FTyNat = "Nat"
  show FTyString = "String"
  show (FTyVar v) = v
  show (FTyList t) = "(List " ++ (show t) ++ ")"
  show (FTyFn t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (FTyProd t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++  ")"
  show (FTySum t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++  ")"
  show FTyUnit = "Unit"
  show FTyVoid = "Void"
  show (FForall x t) = "(forall " ++ d ++ show t ++ ")"
   where d = foldr (\p q -> p ++ " " ++ q) ", " x

mTyToFTy :: MTy -> FTy 
mTyToFTy (TyVar v) = FTyVar v 
mTyToFTy TyNat = FTyNat
mTyToFTy TyString = FTyString
mTyToFTy TyUnit = FTyUnit
mTyToFTy TyVoid = FTyVoid
mTyToFTy (TyList x) = FTyList $ mTyToFTy x
mTyToFTy (TyFn x y) = FTyFn (mTyToFTy x) (mTyToFTy y)
mTyToFTy (TyProd x y) = FTyProd (mTyToFTy x) (mTyToFTy y)
mTyToFTy (TySum x y) = FTySum (mTyToFTy x) (mTyToFTy y)

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
 vars TyNat = []
 vars TyString = []

primTy :: Prim -> TypSch
primTy (PrimStr s) = Forall [] TyString
primTy (PrimNat i) = Forall [] TyNat
primTy Fst = Forall ["x", "y"] $ (TyProd (TyVar "x") (TyVar "y")) `TyFn` (TyVar "x")
primTy Snd = Forall ["x", "y"] $ (TyProd (TyVar "x") (TyVar "y")) `TyFn` (TyVar "y")
primTy Nil = Forall ["t"] $ TyList (TyVar "t")
primTy Cons = Forall ["t"] $ TyFn (TyVar "t") (TyFn (TyList (TyVar "t")) (TyList (TyVar "t")))
primTy TT = Forall [] TyUnit
primTy FF = Forall ["t"] $ TyFn TyVoid (TyVar "t")
primTy Inl = Forall ["x", "y"] $ (TyVar "x") `TyFn` (TyProd (TyVar "x") (TyVar "y"))  
primTy Inr = Forall ["x", "y"] $ (TyVar "y") `TyFn` (TyProd (TyVar "x") (TyVar "y"))
primTy Succ = Forall [] $ TyNat `TyFn` TyNat
primTy Pred = Forall [] $ TyNat `TyFn` TyNat
primTy Pair = Forall ["x", "y"] $ (TyFn (TyVar "x") (TyFn (TyVar "y") (TyProd (TyVar "x") (TyVar "y"))))
primTy If0 = Forall [] $ TyNat `TyFn` (TyNat `TyFn` (TyNat `TyFn` TyNat))
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
       
class Substable a where
  subst :: Subst -> a -> a
  
instance Substable MTy where
 subst f TyNat = TyNat
 subst f TyString = TyString
 subst f TyUnit = TyUnit 
 subst f TyVoid = TyVoid
 subst f (TyList t) = TyList $ subst f t 
 subst f (TyFn t1 t2) = TyFn (subst f t1) (subst f t2) 
 subst f (TyProd t1 t2) = TyProd  (subst f t1) (subst f t2)
 subst f (TySum t1 t2) = TySum  (subst f t1) (subst f t2)
 subst f (TyVar v) = case lookup v f of
                      Nothing -> TyVar v
                      Just y -> y
                      
instance Substable FTy where
 subst f FTyNat = FTyNat
 subst f FTyString = FTyString
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

subst' :: [(Var,FTy)] -> FTy -> FTy 
subst' f FTyNat = FTyNat
subst' f FTyString = FTyString
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
                                

-----------------------------
-- Unification

mgu :: MTy -> MTy -> E Subst
mgu TyNat TyNat = return []
mgu TyString TyString = return[]
mgu (TyList a) (TyList b) = mgu a b
mgu TyUnit TyUnit = return []
mgu TyVoid TyVoid = return []
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
occurs v (TyNat) = return ()
occurs v (TyString) = return ()
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

type E = ErrorT String (State Integer)
type M a = E (Subst, a)

fresh :: E MTy
fresh = do { s <- get; put (s + 1); return $ TyVar $ "v" ++ show s }

inst :: TypSch -> E (MTy,[MTy])
inst (Forall vs ty) = do { vs' <- mapM (\_->fresh) vs; return $ (subst (zip vs vs') ty,  vs') } 
                        
gen :: Ctx -> MTy -> (TypSch, [Var])
gen g t = (Forall vs t , vs)
 where vs = nub $ filter (\v -> not $ elem v (vars g)) (vars t)  

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
w g (Let x e0 e1) = do { (s0, (t , a)) <- w g e0
                       ; let (tt,vs) = gen (subst s0 g) t
                       ; (s1, (t', b)) <- w ((x,tt):subst s0 g) e1                                                                
                       ; return (s1 `o` s0, (t', FApp (FAbs x (tyToFTy $ subst s1 tt) b) (fTyAbs vs a))) }
w g (Letrec' x e0 e1) = do { t0 <- fresh 
                           ; (s0, (t,e0X)) <- w ((x, Forall [] t0):g) e0
                           ; s' <- mgu (subst s0 t0) t 
                           ; let (ww,ww2) = gen (subst (s' `o` s0) g) (subst s' t)
                           ; (s1, (t',e1X)) <- w ((x, ww):subst (s' `o` s0) g) e1
                           ; let e0X' = subst'' [(x, fTyApp (FVar x) $ map FTyVar ww2)] e0X
                           ; let e0X'' = fTyAbs ( ww2) e0X'  
                           ; return (s1 `o` s' `o` s0, (t', FLetrec [(x, subst s1 $ tyToFTy ww, subst (s' `o` s1) e0X'')] e1X)) }
w g (Letrec xe0 e1) = do { t0s <- mapM (\(k,v) -> do { f <- fresh; return (k, f) }) xe0
                         ; let g' = map (\(k,v) -> (k, Forall [] v)) t0s ++ g
                         ; (s0, (ts,e0Xs)) <- w' g' xe0
                         ; s' <- mgu' (map (\(_,v) -> subst s0 v) t0s) ts
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

----------------------------------------
-- Hydra Core support

-- Note: no support for @wisnesky's Prim constructors other than PrimStr and PrimNat
hydraTermToStlc :: Core.Term -> Expr
hydraTermToStlc term = case term of
  Core.TermLiteral lit -> case lit of
    Core.LiteralString s -> Const $ PrimStr s
    Core.LiteralInteger int -> case int of
      Core.IntegerValueBigint n -> Const $ PrimNat n
  Core.TermList els -> foldr (\el acc -> App (App (Const Cons) (hydraTermToStlc el)) acc) (Const Nil) els
  Core.TermVariable (Core.Name v) -> Var v
  Core.TermApplication (Core.Application t1 t2) -> App (hydraTermToStlc t1) (hydraTermToStlc t2)
  Core.TermFunction f -> case f of
    Core.FunctionLambda (Core.Lambda (Core.Name v) body) -> Abs v (hydraTermToStlc body)
  Core.TermLet (Core.Let bindings env) -> Letrec (fieldToStlc <$> bindings) $ hydraTermToStlc env
    where
      fieldToStlc (Core.Field (Core.FieldName v) term) = (v, hydraTermToStlc term)

systemFExprToHydra :: FExpr -> Either String Core.Term
systemFExprToHydra expr = case expr of
  FConst prim -> case prim of
    PrimStr s -> pure $ Core.TermLiteral $ Core.LiteralString s
    PrimNat n -> pure $ Core.TermLiteral $ Core.LiteralInteger $ Core.IntegerValueBigint n
    _ -> Left $ "unsupported primitive: " ++ show prim
    -- Note: other prims are unsupported
  FVar v -> pure $ Core.TermVariable $ Core.Name v
  FApp e1 e2 -> case e1 of
    FApp (FConst Cons) hd -> do
        els <- CM.mapM systemFExprToHydra (hd:(gather e2))
        return $ Core.TermList els
      where
        gather e = case e of
          FConst Nil -> []
          FApp (FApp (FConst Cons) hd) tl -> hd:(gather tl)
    _ -> Core.TermApplication <$> (Core.Application <$> systemFExprToHydra e1 <*> systemFExprToHydra e2)
  -- TODO: annotate with domain type
  FAbs v dom e -> do
    term <- systemFExprToHydra e
    return $ Core.TermFunction $ Core.FunctionLambda (Core.Lambda (Core.Name v) term)
  -- TODO: FTyApp FExpr [FTy]
  -- TODO: FTyAbs [Var] FExpr
  FLetrec bindings env -> Core.TermLet <$>
      (Core.Let <$> CM.mapM bindingToHydra bindings <*> systemFExprToHydra env)
    where
      bindingToHydra (v, ty, term) = do
        hterm <- systemFExprToHydra term
        htyp <- systemFTypeToHydra ty
        -- TODO: attach htyp
        return $ Core.Field (Core.FieldName v) hterm
  _ -> Left $ "unsupported expression: " ++ show expr

systemFTypeToHydra :: FTy -> Either String Core.Type
systemFTypeToHydra ty = case ty of
  FTyVar v -> pure $ Core.TypeVariable $ Core.Name v
  FTyNat -> pure $ Core.TypeLiteral $ Core.LiteralTypeInteger Core.IntegerTypeBigint
  FTyString -> pure $ Core.TypeLiteral $ Core.LiteralTypeString
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
  _ -> Left $ "unsupported type: " ++ show ty

inferWithAlgorithmW :: Core.Term -> IO (Core.Term, Core.Type)
inferWithAlgorithmW term = do
    (fexpr, _) <- inferExpr $ hydraTermToStlc $ wrap term
    let (uexpr, uty) = unwrap fexpr
    hydraTerm <- case systemFExprToHydra uexpr of
      Left err -> fail err
      Right t -> return t
    hydraType <- case systemFTypeToHydra uty of
      Left err -> fail err
      Right t -> return t
    return (hydraTerm, hydraType)
  where
    wrap term = Core.TermLet $ Core.Let ([Core.Field (Core.FieldName "x") term]) $
      Core.TermLiteral $ Core.LiteralString "placeholder"
    unwrap expr = case expr of
      FLetrec bindings env -> case bindings of
        [(_, ty, e)] -> (e, ty)

inferExpr :: Expr -> IO (FExpr, FTy)
inferExpr t = case (fst $ runState (runErrorT (w [] t)) 0) of
  Left e -> fail $ "inference error: " ++ e
  Right (s, (ty, f)) -> case (typeOf [] [] f) of
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
test_1 = Letrec [("foo", Abs "x" $ Var "x")] $ Const $ PrimNat 42

test_2 :: Expr
test_2 =  Let "f" ( (Abs "x" (Var "x"))) $ App (Var "f")  (Const $ PrimNat 0)
 where sng0 = App (Var "sng") (Const $ PrimNat 0)
       sngAlice = App (Var "sng") (Const $ PrimStr "alice")
       body = (Var "sng")
       
test_3 :: Expr
test_3 =  Let "f" (App (Abs "x" (Var "x")) (Const $ PrimNat 0)) (Var "f")  
 where sng0 = App (Var "sng") (Const $ PrimNat 0)
       sngAlice = App (Var "sng") (Const $ PrimStr "alice")

test_4 :: Expr
test_4 = Let "sng" (Abs "x" (App (App (Const Cons) (Var "x")) (Const Nil))) body 
 where 
       body = (Var "sng")

test_5 :: Expr
test_5 = Let "sng" (Abs "x" (App (App (Const Cons) (Var "x")) (Const Nil))) body 
 where sng0 = App (Var "sng") (Const $ PrimNat 0)
       sngAlice = App (Var "sng") (Const $ PrimStr "alice")
       body = App (App (Const Pair) sng0) sngAlice 
       
test_6 :: Expr
test_6 = letrec' "+" (Abs "x" $ Abs "y" $ recCall) twoPlusOne 
 where
   recCall = App (Const Succ) $ App (App (Var "+") (App (Const Pred) (Var "x"))) (Var "y") 
   ifz x y z = App (App (App (Const If0) x) y) z
   twoPlusOne = App (App (Var "+") two) one 
   two = App (Const Succ) one
   one = App (Const Succ) (Const $ PrimNat 0)

test_7 :: Expr
test_7 = letrec' "+" (Abs "x" $ Abs "y" $ recCall) $ twoPlusOne 
 where
   recCall = App (Const Succ) $ App (App (Var "+") (App (Const Pred) (Var "x"))) ( (Var "y"))
   ifz x y z = App (App (App (Const If0) x) y) z
   twoPlusOne = App (App (Var "+") two) one 
   two = App (Const Succ) one
   one = App (Const Succ) (Const $ PrimNat 0)  

test_8 :: Expr
test_8 = letrec' "f" f x 
 where x =  (Var "f")
       f = Abs "x" $ Abs "y" $ App (App (Var "f") (Const $ PrimNat 0)) (Var "x") 

test_9 :: Expr
test_9 = Letrec [("f", f), ("g", g)] x 
 where x =  App (App (Const $ Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "f") (Const $ PrimNat 0)) (Var "x")        
       g = Abs "xx" $ Abs "yy" $ App (App (Var "g") (Const $ PrimNat 0)) (Var "xx")   

test_10 :: Expr
test_10 = Letrec [("f", f), ("g", g)] b
 where b = App (App (Const Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (Const $ PrimNat 0)) (Var "x") 
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (Var "v")) (Const $ PrimNat 0) 

test_11 :: Expr
test_11 = Letrec [("f", f), ("g", g)] b
 where b = App (App (Const Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (Const $ PrimNat 0)) (Const $ PrimNat 0)
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (Var "v")) (Const $ PrimNat 0) 

test_12 :: Expr
test_12 = Letrec [("f", f), ("g", g)] b
 where b = App (App (Const Pair) (Var "f")) (Var "g")
       f = Abs "x" $ Abs "y" $ App (App (Var "g") (Const $ PrimNat 0)) (Var "x") 
       g = Abs "u" $ Abs "v" $ App (App (Var "f") (Const $ PrimNat 0)) (Const $ PrimNat 0) 
