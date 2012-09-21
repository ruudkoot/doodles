{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module CallByName where

import Control.Monad
import Control.Monad.State

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S

import Fresh
import Printing
import Util

import Syntax
import Analysis

-- | Annotated types

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
    
-- | Environments

type LazyAnnTyEnv = M.Map Ident (LazyAnnTy, Eff)

-- | Substitutions

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
    LazyAnnSubst _ ev $$$@ eff = flattenSetOfSets (S.map f eff)
        where f (EffVar u) | Just eff' <- M.lookup u ev = eff'
              f  EffCrash  = S.singleton EffCrash

-- | Unification

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
unify__ _ _
    = error "cannot unify effects"

-- | Inference

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
