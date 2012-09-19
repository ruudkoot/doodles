{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Main where

import Control.Monad       hiding (join)
import Control.Monad.State hiding (join)

import qualified Data.List as L
import qualified Data.Map  as M
import           Data.Maybe
import qualified Data.Set  as S

import Fresh
import Parsing
import Printing

-- | Syntax

data Con
    = Bool Bool
    | Int  Int
    deriving (Eq, Ord, Show)

data Expr
    = Var Ident
    | Con Con
    | Abs Ident Expr
    | App Expr Expr
    | Let Ident Expr Expr
    | Crash
    | Close Expr Env
    deriving (Eq, Ord, Show)

instance LaTeX Expr where
    latex (Var x)            = x
    latex (Con (Bool True )) = "\\mathbf{True}"    
    latex (Con (Bool False)) = "\\mathbf{False}"
    latex (Con (Int n     )) = show n
    latex (Abs x e         ) = "\\lambda " ++ x ++ ".\\ " ++ latex e
    latex (App e1 e2       ) = latex e1 ++ "\\ " ++ latex e2
    latex (Let x e1 e2     ) = "\\mathbf{let}\\ " ++ x ++ "\\ \\mathbf{=}\\ " ++ latex e1 ++ "\\ \\mathbf{in}\\ " ++ latex e2
    latex (Crash           ) = "\\lightning"
    latex (Close e env     ) = "\\mathbf{close}\\ " ++ latex e ++ "\\ \\mathbf{in}\\ " ++ latex env
    
-- | Dynamics

type Env = M.Map Ident Expr

instance LaTeX Env where
    latex env = case M.toList env of
                    []   -> "\\epsilon"
                    env' -> "\\left[" ++ concat (L.intersperse ", " (map (\(x,e) -> x ++ "\\mapsto" ++ latex e) env'))++ "\\right]"

-- * Call-by-value

cbv :: Expr -> Expr
cbv = cbv' M.empty

cbv' :: Env -> Expr -> Expr
cbv' env (Var x)
    = fromJust (M.lookup x env)
cbv' env (Con c)
    = Con c
cbv' env (Abs x e)
    = Close (Abs x e) env
cbv' env (App e1 e2)
    = case cbv' env e2 of
        Crash -> Crash
        v2    -> case cbv' env e1 of
                    Crash -> Crash
                    Close (Abs x e1') env' -> cbv' (M.insert x v2 env') e1'
cbv' env (Let x e1 e2)
    = case cbv' env e1 of
        Crash -> Crash
        v1    -> cbv' (M.insert x v1 env) e2
cbv' env Crash
    = Crash
    
-- Call-by-name
    
cbn :: Expr -> Expr
cbn = cbn' M.empty

cbn' :: Env -> Expr -> Expr
cbn' env (Var x)
    = fromJust (M.lookup x env)
cbn' env (Con c)
    = Close (Con c) env
cbn' env (Abs x e)
    = Close (Abs x e) env
cbn' env (App e1 e2)
    = case cbn' env e1 of
        Crash                  -> Crash
        Close (Abs x e1') env' -> cbn' (M.insert x e2 env') e1'
        x                      -> error $ show x
cbn' env (Let x e1 e2)
    = cbn' (M.insert x (Close e1 env) env) e2
cbn' env Crash
    = Crash

-- | Statics

-- * Types

data TyCon
    = TyBool
    | TyInt
    deriving (Eq, Ord, Show)

data Ty
    = TyVar Ident
    | TyCon TyCon
    | TyFun Ty Ty
    deriving (Eq, Ord, Show)
    
instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar a)
    
instance LaTeX Ty where
    latex (TyVar a     ) = "\\tau" ++ a
    latex (TyCon TyBool) = "\\mathbf{Bool}"
    latex (TyCon TyInt ) = "\\mathbf{Int}"
    latex (TyFun t1 t2 ) = "(" ++ latex t1 ++ "\\rightarrow" ++ latex t2 ++ ")"

-- * Free variables

class FreeVars t where
    ftv :: t -> S.Set Ident

instance FreeVars Ty where
    ftv (TyCon _   ) = S.empty
    ftv (TyFun t t') = ftv t `S.union` ftv t'
    ftv (TyVar a   ) = S.singleton a

-- * Substitutions

newtype Subst = Subst (M.Map Ident Ty)

idSubst :: Subst
idSubst = Subst M.empty

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (Subst tv1) (Subst tv2)
            = Subst (M.unionWith (error "type variables not distinct") tv1 tv2)
                    
class Substitute t where
    ($@) :: Subst -> t -> t
    
instance Substitute Subst where
    subst $@ (Subst tv) = Subst (M.map (subst $@) tv)

instance Substitute Ty where
    Subst tv_ $@ (TyVar a)    | Just t <- M.lookup a tv_ = t
    subst     $@ (TyFun t t') = TyFun (subst $@ t) (subst $@ t')
    _         $@ x            = x

-- * Unification

unify :: Ty -> Ty -> Subst
unify (TyCon c1) (TyCon c2)
    | c1 == c2 = idSubst
unify (TyVar a) (TyVar a')
    = Subst (M.singleton a (TyVar a'))
unify (TyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = Subst (M.singleton a t)
unify t (TyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = Subst (M.singleton a t)
unify (TyFun t1 t2) (TyFun t'1 t'2)
    = let subst1 = unify t1 t'1
          subst2 = unify (subst1 $@ t2) (subst1 $@ t'2)
       in subst2 $. subst1
unify _ _
    = error "cannot unify"

-- * Type inference

type TyEnv = M.Map Ident Ty

instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env

infer :: TyEnv -> Expr -> State [Ident] (Ty, Subst)
infer env (Var x)
    | Just t <- M.lookup x env = return (t, idSubst)
    | otherwise                = error "variable not in scope"
infer env (Con c)
    = case c of
        Bool _ -> return (TyCon TyBool, idSubst)
        Int  _ -> return (TyCon TyInt, idSubst)
infer env (Abs x e0)
    = do ax <- fresh
         (t0, subst0) <- infer (M.insert x ax env) e0
         return (TyFun (subst0 $@ ax) t0, subst0)
infer env (App e1 e2)
    = do (t1, subst1) <- infer env e1
         (t2, subst2) <- infer (subst1 $@ env) e2
         a <- fresh
         let subst3 = unify (subst2 $@ t1) (TyFun t2 a)
         return (subst3 $@ a, subst3 $. subst2 $. subst1)
infer env (Let x e1 e2)
    = do (t1, subst1) <- infer env e1
         (t2, subst2) <- infer (M.insert x t1 (subst1 $@ env)) e2
         return (t2, subst2 $. subst1)
infer env Crash
    = do a <- fresh
         return (a, idSubst)
         
-- | Analysis

-- * Effects

data EffCon
    = EffNone
    | EffCrash
    deriving (Eq, Ord, Show)
    
join :: EffCon -> EffCon -> EffCon
join EffNone EffNone = EffNone
join _       _       = EffCrash

instance LaTeX EffCon where
    latex EffNone  = "\\emptyset"
    latex EffCrash = "\\lightning"
    
data Eff
    = EffUnif Ident
    | EffCon  EffCon
    deriving (Eq, Ord, Show)
    
instance Fresh Eff where
    fresh = do a <- fresh
               return (EffUnif a)

instance LaTeX Eff where
    latex (EffUnif u) = "\\varphi" ++ u
    latex (EffCon  c) = latex c
    
effcon :: Eff -> EffCon
effcon (EffCon c) = c
effcon _          = error "effect not a constant"

-- * Annotated types (call-by-value)

data AnnTy
    = AnnTyVar Ident
    | AnnTyCon TyCon
    | AnnTyFun AnnTy Eff AnnTy
    deriving (Eq, Ord, Show)
    
instance Fresh AnnTy where
    fresh = do a <- fresh
               return (AnnTyVar a)
               
instance FreeVars AnnTy where
    ftv (AnnTyCon _     ) = S.empty
    ftv (AnnTyFun t _ t') = ftv t `S.union` ftv t'
    ftv (AnnTyVar a     ) = S.singleton a
    
instance LaTeX AnnTy where
    latex (AnnTyVar a        ) = "\\widehat\\tau" ++ a
    latex (AnnTyCon TyBool   ) = "\\mathbf{Bool}"
    latex (AnnTyCon TyInt    ) = "\\mathbf{Int}"
    latex (AnnTyFun t1 eff t2) = "(" ++ latex t1 ++ "\\overset{" ++ latex eff ++ "}{\\rightarrow}" ++ latex t2 ++ ")"
    
-- * Environments (call-by-value)

type AnnTyEnv = M.Map Ident AnnTy

-- * Substitutions (call-by-value)

data AnnSubst = AnnSubst (M.Map Ident AnnTy) (M.Map Ident Eff)

idAnnSubst :: AnnSubst
idAnnSubst = AnnSubst M.empty M.empty

($$.) :: AnnSubst -> AnnSubst -> AnnSubst
s2 $$. s1 = (s2 $$@ s1) `substUnion` s2
    where 
        substUnion (AnnSubst tv1 ev1) (AnnSubst tv2 ev2)
            = AnnSubst (M.unionWith (error "type variables not distinct") tv1 tv2)
                       (M.unionWith (error "effect variables not distinct") ev1 ev2)
                    
class AnnSubstitute t where
    ($$@) :: AnnSubst -> t -> t
    
instance AnnSubstitute AnnSubst where
    subst $$@ (AnnSubst tv ev) = AnnSubst (M.map (subst $$@) tv) (M.map (subst $$@) ev)

instance AnnSubstitute AnnTy where
    AnnSubst tv _ $$@ (AnnTyVar a)
        | Just t <- M.lookup a tv = t
    subst         $$@ (AnnTyFun t eff t')
        = AnnTyFun (subst $$@ t) (subst $$@ eff) (subst $$@ t')
    _             $$@ x
        = x

instance AnnSubstitute AnnTyEnv where
    subst $$@ env = M.map (subst $$@) env

instance AnnSubstitute Eff where
    AnnSubst _ ev $$@ (EffUnif u)
        | Just e <- M.lookup u ev = e
    _             $$@ x
        = x

-- * Unification (call-by-value)

unify' :: AnnTy -> AnnTy -> AnnSubst
unify' (AnnTyCon c1) (AnnTyCon c2)
    | c1 == c2 = idAnnSubst
unify' (AnnTyVar a) (AnnTyVar a')
    = AnnSubst (M.singleton a (AnnTyVar a')) M.empty
unify' (AnnTyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = AnnSubst (M.singleton a t) M.empty
unify' t (AnnTyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = AnnSubst (M.singleton a t) M.empty
unify' (AnnTyFun t1 eff t2) (AnnTyFun t'1 eff' t'2)
    = let subst1 = unify' t1 t'1
          subst2 = unify' (subst1 $$@ t2) (subst1 $$@ t'2)
          subst3 = unify'' eff eff'
       in subst3 $$. subst2 $$. subst1
unify' _ _
    = error "cannot unify types"

unify'' :: Eff -> Eff -> AnnSubst
unify'' (EffUnif u1) (EffUnif u2)
    = AnnSubst M.empty (M.singleton u1 (EffUnif u2))
unify'' (EffUnif u) e
    = AnnSubst M.empty (M.singleton u e)
unify'' e (EffUnif u)
    = AnnSubst M.empty (M.singleton u e)
unify'' (EffCon c1) (EffCon c2)
    | c1 == c2 = idAnnSubst
unify'' _ _
    = error "cannot unify effects"


-- * Inference (call-by-value)

analyzeCBV :: AnnTyEnv -> Expr -> State [Ident] (AnnTy, EffCon, AnnSubst)
analyzeCBV env (Var x)
    | Just t <- M.lookup x env = return (t, EffNone, idAnnSubst)
    | otherwise                = error "variable not in scope"
analyzeCBV env (Con c)
    = case c of
        Bool _ -> return (AnnTyCon TyBool, EffNone, idAnnSubst)
        Int  _ -> return (AnnTyCon TyInt, EffNone, idAnnSubst)
analyzeCBV env (Abs x e0)
    = do ax <- fresh
         (t0, eff0, subst0) <- analyzeCBV (M.insert x ax env) e0
         return (AnnTyFun (subst0 $$@ ax) (EffCon eff0) t0, EffNone, subst0)
analyzeCBV env (App e1 e2)
    = do (t1, eff1, subst1) <- analyzeCBV env e1
         (t2, eff2, subst2) <- analyzeCBV (subst1 $$@ env) e2
         a <- fresh
         u <- fresh
         let subst3 = unify' (subst2 $$@ t1) (AnnTyFun t2 u a)
         return (subst3 $$@ a, effcon (subst3 $$@ u) `join` eff1 `join` eff2, subst3 $$. subst2 $$. subst1)
analyzeCBV env (Let x e1 e2)
    = do (t1, eff1, subst1) <- analyzeCBV env e1
         (t2, eff2, subst2) <- analyzeCBV (M.insert x t1 (subst1 $$@ env)) e2
         return (t2, {- subst2 $@@ -} eff1 `join` eff2, subst2 $$. subst1)
analyzeCBV env Crash
    = do a <- fresh
         return (a, EffCrash, idAnnSubst)

-- * Annotated types (call-by-name)

data LazyAnnTy
    = LazyAnnTyVar Ident
    | LazyAnnTyCon TyCon
    | LazyAnnTyFun LazyAnnTy Eff LazyAnnTy Eff
    deriving (Eq, Ord, Show)
    
instance Fresh LazyAnnTy where
    fresh = do a <- fresh
               return (LazyAnnTyVar a)
               
instance FreeVars LazyAnnTy where
    ftv (LazyAnnTyCon _       ) = S.empty
    ftv (LazyAnnTyFun t _ t' _) = ftv t `S.union` ftv t'
    ftv (LazyAnnTyVar a       ) = S.singleton a
    
instance LaTeX LazyAnnTy where
    latex (LazyAnnTyVar a              ) = "\\widehat\\tau" ++ a
    latex (LazyAnnTyCon TyBool         ) = "\\mathbf{Bool}"
    latex (LazyAnnTyCon TyInt          ) = "\\mathbf{Int}"
    latex (LazyAnnTyFun t1 eff1 t2 eff2) = "(" ++ latex t1 ++ "@" ++ latex eff1 ++ "\\rightarrow" ++ latex t2 ++ "@" ++ latex eff2 ++ ")"
    
-- * Environments (call-by-name)

type LazyAnnTyEnv = M.Map Ident (LazyAnnTy, Eff)

-- * Substitutions (call-by-name)

data LazyAnnSubst = LazyAnnSubst (M.Map Ident LazyAnnTy) (M.Map Ident Eff)

idLazyAnnSubst :: LazyAnnSubst
idLazyAnnSubst = LazyAnnSubst M.empty M.empty

($$$.) :: LazyAnnSubst -> LazyAnnSubst -> LazyAnnSubst
s2 $$$. s1 = (s2 $$$@ s1) `substUnion` s2
    where 
        substUnion (LazyAnnSubst tv1 ev1) (LazyAnnSubst tv2 ev2)
            = LazyAnnSubst (M.unionWith (error "type variables not distinct") tv1 tv2)
                           (M.unionWith (error "effect variables not distinct") ev1 ev2)
                    
class LazyAnnSubstitute t where
    ($$$@) :: LazyAnnSubst -> t -> t
    
instance LazyAnnSubstitute LazyAnnSubst where
    subst $$$@ (LazyAnnSubst tv ev) = LazyAnnSubst (M.map (subst $$$@) tv) (M.map (subst $$$@) ev)

instance LazyAnnSubstitute LazyAnnTy where
    LazyAnnSubst tv _ $$$@ (LazyAnnTyVar a)
        | Just t <- M.lookup a tv = t
    subst             $$$@ (LazyAnnTyFun t eff t' eff')
        = LazyAnnTyFun (subst $$$@ t) (subst $$$@ eff) (subst $$$@ t') (subst $$$@ eff')
    _                 $$$@ x
        = x

instance LazyAnnSubstitute LazyAnnTyEnv where
    subst $$$@ env = M.map (\(t, eff) -> (subst $$$@ t, subst $$$@ eff)) env

instance LazyAnnSubstitute Eff where
    LazyAnnSubst _ ev $$$@ (EffUnif u)
        | Just e <- M.lookup u ev = e
    _             $$$@ x
        = x

-- * Unification (call-by-name)

unify_ :: LazyAnnTy -> LazyAnnTy -> LazyAnnSubst
unify_ (LazyAnnTyCon c1) (LazyAnnTyCon c2)
    | c1 == c2 = idLazyAnnSubst
unify_ (LazyAnnTyVar a) (LazyAnnTyVar a')
    = LazyAnnSubst (M.singleton a (LazyAnnTyVar a')) M.empty
unify_ (LazyAnnTyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = LazyAnnSubst (M.singleton a t) M.empty
unify_ t (LazyAnnTyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = LazyAnnSubst (M.singleton a t) M.empty
unify_ (LazyAnnTyFun t1 eff1 t2 eff2) (LazyAnnTyFun t'1 eff'1 t'2 eff'2)
    = let subst1 = unify_ t1 t'1
          subst2 = unify_ (subst1 $$$@ t2) (subst1 $$$@ t'2)
          subst3 = unify__ eff1 eff'1
          subst4 = unify__ eff2 eff'2
       in subst4 $$$. subst3 $$$. subst2 $$$. subst1
unify_ _ _
    = error "cannot unify types"

unify__ :: Eff -> Eff -> LazyAnnSubst
unify__ (EffUnif u1) (EffUnif u2)
    = LazyAnnSubst M.empty (M.singleton u1 (EffUnif u2))
unify__ (EffUnif u) e
    = LazyAnnSubst M.empty (M.singleton u e)
unify__ e (EffUnif u)
    = LazyAnnSubst M.empty (M.singleton u e)
unify__ (EffCon c1) (EffCon c2)
    | c1 == c2 = idLazyAnnSubst
unify__ _ _
    = error "cannot unify effects"

-- * Inference (call-by-name)

analyzeCBN :: LazyAnnTyEnv -> Expr -> State [Ident] (LazyAnnTy, EffCon, LazyAnnSubst)
analyzeCBN env (Var x)
    | Just (t, eff) <- M.lookup x env = return (t, effcon eff, idLazyAnnSubst)
    | otherwise                       = error "variable not in scope"
analyzeCBN env (Con c)
    = case c of
        Bool _ -> return (LazyAnnTyCon TyBool, EffNone, idLazyAnnSubst)
        Int  _ -> return (LazyAnnTyCon TyInt, EffNone, idLazyAnnSubst)
analyzeCBN env (Abs x e0)
    = do a <- fresh
         u <- fresh
         (t0, eff0, subst0) <- analyzeCBN (M.insert x (a, u) env) e0
         return (LazyAnnTyFun (subst0 $$$@ a) (subst0 $$$@ u) t0 (EffCon eff0), EffNone, subst0)
analyzeCBN env (App e1 e2)
    = do (t1, eff1, subst1) <- analyzeCBN env e1
         (t2, eff2, subst2) <- analyzeCBN (subst1 $$$@ env) e2
         a <- fresh
         u <- fresh
         let subst3 = unify_ (subst2 $$$@ t1) (LazyAnnTyFun t2 (EffCon eff2) a u)
         return (subst3 $$$@ a, effcon u `join` {- subst $@@ -} eff1, subst3 $$$. subst2 $$$. subst1)
analyzeCBN env (Let x e1 e2)
    = do (t1, eff1, subst1) <- analyzeCBN env e1
         (t2, eff2, subst2) <- analyzeCBN (M.insert x (t1, EffCon eff1) (subst1 $$$@ env)) e2
         return (t2, eff2, subst2 $$$. subst1)
analyzeCBN env Crash
    = do a <- fresh
         return (a, EffCrash, idLazyAnnSubst)
    
-- | Examples

main
    = do putStrLn preamble
         example "Example 1" ex1
         example "Example 2" ex2
         example "Example 3" ex3
         putStrLn postamble
          
example name ex
    = do putStrLn ("\\paragraph{" ++ name ++ "}")
         putStrLn "\\begin{gather}"
         putStrLn (latex ex ++ newline)
         let ((t, subst), _) = runState (infer M.empty ex) freshIdents
         putStrLn (latex t ++ newline)
         let ((t, eff, subst), _) = runState (analyzeCBV M.empty ex) freshIdents
         putStrLn ("(" ++ latex t ++ ", " ++ latex eff ++ ")" ++ newline)
         putStrLn (latex (cbv ex) ++ newline)
         putStrLn (latex (cbn ex))
         putStrLn "\\end{gather}"

ex1 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Int 3))) (Con (Bool False)))
ex2 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Bool True))) Crash)
ex3 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (Var "const")
ex4 = Let "id" (Abs "x" (Var "x")) (App (Var "id") (Var "id")) -- needs let-polymorphism
