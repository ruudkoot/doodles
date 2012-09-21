{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module CallByValue where

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
    latex (AnnTyFun t1 eff t2) = "\\left(" ++ latex t1
                                 ++ "\\xrightarrow{" ++ latex eff ++ "}"
                                 ++ latex t2 ++ "\\right)"
    
-- | Environments

type AnnTyEnv = M.Map Ident AnnTy

-- | Substitutions

data AnnSubst = AnnSubst  (M.Map Ident AnnTy) (M.Map Ident Ident)

idAnnSubst :: AnnSubst
idAnnSubst = AnnSubst M.empty M.empty

($$.) :: AnnSubst -> AnnSubst -> AnnSubst
s2 $$. s1 = (s2 $$@ s1) `substUnion` s2
    where 
        substUnion (AnnSubst tv1 ev1) (AnnSubst tv2 ev2)
            = AnnSubst (M.unionWith (error "type variables not distinct") tv1 tv2)
                       (M.unionWith (error "effect variables not distinct") ev1 ev2)

data AnnSubst' = AnnSubst' (M.Map Ident Eff)

idAnnSubst' :: AnnSubst'
idAnnSubst' = AnnSubst' M.empty

($$.#) :: AnnSubst' -> AnnSubst' -> AnnSubst'
s2 $$.# s1 = (s2 $$@# s1) `substUnion` s2
    where 
        substUnion (AnnSubst' ev1) (AnnSubst' ev2)
            = AnnSubst' (M.unionWith (error "effect variables not distinct") ev1 ev2)

instance LaTeX AnnSubst where
    latex (AnnSubst tv ev)
        | M.null tv && M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ f "\\widehat\\tau" "" tv ++ "; "
                      ++ f "\\dot\\varphi" "\\dot\\varphi" ev ++ "\\right]"
            where f l r = L.intercalate ", " 
                          . map (\(k, v) -> l ++ latex k ++ "\\mapsto"
                                              ++ r ++ latex v)
                          . M.toList
                          
instance LaTeX AnnSubst' where
    latex (AnnSubst' ev)
        | M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ f "\\dot\\varphi" "\\dot\\varphi" ev ++ "\\right]"
            where f l r = L.intercalate ", " 
                          . map (\(k, v) -> l ++ latex k ++ "\\mapsto"
                                              ++ r ++ latex v)
                          . M.toList

class AnnSubstitute t where
    ($$@) :: AnnSubst -> t -> t
    
class AnnSubstitute' t where
    ($$@#) :: AnnSubst' -> t -> t
    
instance AnnSubstitute AnnSubst where
    subst $$@ (AnnSubst tv ev)
        = AnnSubst (M.map (subst $$@) tv) (M.map (subst $$@) ev)
     
instance AnnSubstitute' AnnSubst' where
    subst $$@# (AnnSubst' ev)
        = AnnSubst' (M.map (subst $$@#) ev)       
    
instance AnnSubstitute AnnTy where
    AnnSubst tv _ $$@ (AnnTyVar a)
        | Just t <- M.lookup a tv = t
    subst         $$@ (AnnTyFun t eff t')
        = AnnTyFun (subst $$@ t) (subst $$@ eff) (subst $$@ t')
    _             $$@ x
        = x

instance AnnSubstitute AnnTyEnv where
    subst $$@ env = M.map (subst $$@) env
    
instance AnnSubstitute Eff' where
    AnnSubst _ ev $$@ (EffVar v) | Just u <- M.lookup v ev = EffVar u
    _             $$@ x          = x

instance AnnSubstitute Ident where
    -- FIXME: the identifiers are assumed to be from EffUnif
    AnnSubst _ ev $$@ u | Just u' <- M.lookup u ev = u'
                        | otherwise                = u

instance AnnSubstitute Eff where
    AnnSubst _ ev $$@ (EffUnif u) | Just eff' <- M.lookup u ev = EffUnif eff'
                                  | otherwise                  = EffUnif u
    subst         $$@ (Eff eff)   = Eff (S.map (subst $$@) eff)
    
instance AnnSubstitute' Eff where
    AnnSubst' ev $$@# (EffUnif u) | Just eff' <- M.lookup u ev = eff'
                                  | otherwise                  = error "non-covering substitution"
    AnnSubst' ev $$@# (Eff eff)   = Eff (flattenSetOfSets (S.map f eff))
      where f (EffVar u) | Just (Eff eff') <- M.lookup u ev = eff'
                         | otherwise = S.singleton (EffVar u)
            f  EffCrash  = S.singleton EffCrash

instance AnnSubstitute Constr' where
    subst $$@ k@(u :>: eff) = let Eff eff' = subst $$@ (Eff eff)
                               in (subst $$@ u) :>: eff'

instance AnnSubstitute Constr where
    subst $$@ k = S.map (subst $$@) k

-- | Unification

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
    = AnnSubst M.empty (M.singleton u1 u2)
unify'' _ _
    = error "cannot unify effects"

-- | Inference

analyzeCBV :: AnnTyEnv -> Expr -> State [Ident] (AnnTy, Eff, AnnSubst, Constr)
analyzeCBV env (Var x)
    | Just t <- M.lookup x env = do u <- fresh
                                    return (t, EffUnif u, idAnnSubst, S.empty)
    | otherwise                = error "variable not in scope"
analyzeCBV env (Con c)
    = do u <- fresh
         case c of
            Bool _ -> return (AnnTyCon TyBool, u, idAnnSubst, S.empty)
            Int  _ -> return (AnnTyCon TyInt , u, idAnnSubst, S.empty)
analyzeCBV env (Abs x e0)
    = do ax <- fresh
         (t0, eff0, subst0, k0) <- analyzeCBV (M.insert x ax env) e0
         u <- fresh
         return (AnnTyFun (subst0 $$@ ax) eff0 t0, u, subst0, k0)
analyzeCBV env (App e1 e2)
    = do (t1, eff1, subst1, k1) <- analyzeCBV             env  e1
         (t2, eff2, subst2, k2) <- analyzeCBV (subst1 $$@ env) e2
         a <- fresh
         u <- fresh
         let subst3 = unify' (subst2 $$@ t1) (AnnTyFun t2 u a)
         u' <- fresh
         return ( subst3 $$@ a, EffUnif u', subst3 $$. subst2 $$. subst1
                , S.singleton (u' :>: effect [ subst3 $$@ u
                                             , subst3 $$@ (subst2 $$@ eff1)
                                             , subst3 $$@             eff2 ])
                  `S.union` (subst3 $$@ (subst2 $$@ k1)) `S.union` (subst3 $$@ k2) )
analyzeCBV env (Let x e1 e2)
    = do (t1, eff1, subst1, k1) <- analyzeCBV                            env   e1
         (t2, eff2, subst2, k2) <- analyzeCBV (M.insert x t1 (subst1 $$@ env)) e2
         u <- fresh
         return ( t2, EffUnif u, subst2 $$. subst1
                , S.singleton (u :>: effect [subst2 $$@ eff1, eff2])
                 `S.union` (subst2 $$@ k1) `S.union` k2              )
analyzeCBV env Crash
    = do a <- fresh
         u <- fresh
         return (a, EffUnif u, idAnnSubst, S.singleton (u :>: S.singleton EffCrash))
         
-- | Constraint solver (Talpin and Jouvelot style)

bar :: Constr -> AnnSubst'
bar = S.foldr (\(u :>: eff) r -> AnnSubst' (M.singleton u (r $$@# (Eff (S.singleton (EffVar u) `S.union` eff)))) $$.# r) idAnnSubst'
