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

data Ty
    = TyVar Ident
    | TyCon TyCon
    | TyFun Ty Eff Ty Eff
    deriving (Eq, Ord, Show)
    
instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar a)
               
instance FreeVars Ty where
    ftv (TyCon _       ) = S.empty
    ftv (TyFun t _ t' _) = ftv t `S.union` ftv t'
    ftv (TyVar a       ) = S.singleton a
    
instance LaTeX Ty where
    latex (TyVar a              ) = "\\widehat\\tau" ++ a
    latex (TyCon TyBool         ) = "\\mathbf{Bool}"
    latex (TyCon TyInt          ) = "\\mathbf{Int}"
    latex (TyFun t1 eff1 t2 eff2) = "\\left(" ++ latex t1
                                    ++ "@" ++ latex eff1
                                    ++ "\\rightarrow" ++ latex t2
                                    ++ "@" ++ latex eff2 ++ "\\right)"

-- | Environments

type TyEnv = M.Map Ident (Ty, Eff)

-- | Substitutions

data Subst = Subst (M.Map Ident Ty) (M.Map Ident Ident)

idSubst :: Subst
idSubst = Subst M.empty M.empty

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (Subst tv1 ev1) (Subst tv2 ev2)
            = Subst (M.unionWith (error "type variables not distinct") tv1 tv2)
                           (M.unionWith (error "effect variables not distinct") ev1 ev2)
                    
class Substitute t where
    ($@) :: Subst -> t -> t
    
instance Substitute Subst where
    subst $@ (Subst tv ev) = Subst (M.map (subst $@) tv) (M.map (subst $@) ev)

instance Substitute Ty where
    Subst tv _ $@ (TyVar a)
        | Just t <- M.lookup a tv = t
    subst             $@ (TyFun t eff t' eff')
        = TyFun (subst $@ t) (subst $@ eff) (subst $@ t') (subst $@ eff')
    _                 $@ x
        = x

instance Substitute TyEnv where
    subst $@ env = M.map (\(t, eff) -> (subst $@ t, subst $@ eff)) env

instance Substitute Eff where
    Subst _ ev $@ eff = flattenSetOfSets (S.map f eff)
        where f (EffVar u) | Just eff' <- M.lookup u ev = eff'
              f  EffCrash  = S.singleton EffCrash

-- | Unification

unify :: Ty -> Ty -> Subst
unify (TyCon c1) (TyCon c2)
    | c1 == c2 = idSubst
unify (TyVar a) (TyVar a')
    = Subst (M.singleton a (TyVar a')) M.empty
unify (TyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = Subst (M.singleton a t) M.empty
unify t (TyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = Subst (M.singleton a t) M.empty
unify (TyFun t1 eff1 t2 eff2) (TyFun t'1 eff'1 t'2 eff'2)
    = let subst1 = unify t1 t'1
          subst2 = unify (subst1 $@ t2) (subst1 $@ t'2)
          subst3 = unify' eff1 eff'1
          subst4 = unify' eff2 eff'2
       in subst4 $. subst3 $. subst2 $. subst1
unify _ _
    = error "cannot unify types"

unify' :: Eff -> Eff -> Subst
unify' (EffUnif u1) (EffUnif u2)
    = Subst M.empty (M.singleton u1 (EffUnif u2))
unify' _ _
    = error "cannot unify effects"

-- | Inference

infer :: TyEnv -> Expr -> State [Ident] (Ty, EffCon, Subst)
infer env (Var x)
    | Just (t, eff) <- M.lookup x env = return (t, effcon eff, idSubst)
    | otherwise                       = error "variable not in scope"
infer env (Con c)
    = case c of
        Bool _ -> return (TyCon TyBool, EffNone, idSubst)
        Int  _ -> return (TyCon TyInt, EffNone, idSubst)
infer env (Abs x e0)
    = do a <- fresh
         u <- fresh
         (t0, eff0, subst0) <- infer (M.insert x (a, u) env) e0
         return (TyFun (subst0 $@ a) (subst0 $@ u) t0 (EffCon eff0), EffNone, subst0)
infer env (App e1 e2)
    = do (t1, eff1, subst1) <- infer env e1
         (t2, eff2, subst2) <- infer (subst1 $@ env) e2
         a <- fresh
         u <- fresh
         let subst3 = unify (subst2 $@ t1) (TyFun t2 (EffCon eff2) a u)
         return (subst3 $@ a, effcon u `join` {- subst $@@ -} eff1, subst3 $. subst2 $. subst1)
infer env (Let x e1 e2)
    = do (t1, eff1, subst1) <- infer env e1
         (t2, eff2, subst2) <- infer (M.insert x (t1, EffCon eff1) (subst1 $@ env)) e2
         return (t2, eff2, subst2 $. subst1)
infer env Crash
    = do a <- fresh
         return (a, EffCrash, idSubst)
