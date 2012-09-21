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

type TyEnv = M.Map Ident (Ty, Eff, Constr)

-- | Substitutions

data Subst  = Subst  (M.Map Ident Ty) (M.Map Ident Ident)
data Subst' = Subst'                  (M.Map Ident Eff  )

idSubst :: Subst
idSubst = Subst M.empty M.empty

idSubst' :: Subst'
idSubst' = Subst' M.empty

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (Subst tv1 ev1) (Subst tv2 ev2)
            = Subst (M.unionWith (error "type variables not distinct"  ) tv1 tv2)
                    (M.unionWith (error "effect variables not distinct") ev1 ev2)

($*.) :: Subst' -> Subst' -> Subst'
s2 $*. s1 = (s2 $*@ s1) `substUnion` s2
    where 
        substUnion (Subst' ev1) (Subst' ev2)
            = Subst' (M.unionWith (error "effect variables not distinct") ev1 ev2)

instance LaTeX Subst where
    latex (Subst tv ev)
        | M.null tv && M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ f "\\widehat\\tau" "" tv ++ "; "
                      ++ f "\\dot\\varphi" "\\dot\\varphi" ev ++ "\\right]"
            where f l r = L.intercalate ", " 
                          . map (\(k, v) -> l ++ latex k ++ "\\mapsto"
                                              ++ r ++ latex v)
                          . M.toList

instance LaTeX Subst' where
    latex (Subst' ev)
        | M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ f "\\dot\\varphi" "" ev ++ "\\right]"
            where f l r = L.intercalate ", " 
                          . map (\(k, v) -> l ++ latex k ++ "\\mapsto"
                                              ++ r ++ latex v)
                          . M.toList

class Substitute t where
    ($@) :: Subst -> t -> t
    
class Substitute' t where
    ($*@) :: Subst' -> t -> t
    
instance Substitute Subst where
    subst $@ (Subst tv ev)
        = Subst (M.map (subst $@) tv) (M.map (subst $@) ev)
     
instance Substitute' Subst' where
    subst $*@ (Subst' ev)
        = Subst' (M.map (subst $*@) ev)

instance Substitute Ty where
    Subst tv _ $@ (TyVar a)
        | Just t <- M.lookup a tv = t
    subst      $@ (TyFun t eff t' eff')
        = TyFun (subst $@ t) (subst $@ eff) (subst $@ t') (subst $@ eff')
    _          $@ x
        = x

instance Substitute TyEnv where
    subst $@ env = M.map (\(t, eff, k) -> (subst $@ t, subst $@ eff, subst $@ k)) env

instance Substitute Eff' where
    Subst _ ev $@ (EffVar v) | Just u <- M.lookup v ev = EffVar u
    _          $@ x          = x

instance Substitute Ident where
    -- FIXME: the identifiers are assumed to be from EffUnif
    Subst _ ev $@ u | Just u' <- M.lookup u ev = u'
                    | otherwise                = u

instance Substitute Eff where
    Subst _ ev $@ (EffUnif u) | Just eff' <- M.lookup u ev = EffUnif eff'
                              | otherwise                  = EffUnif u
    subst      $@ (Eff eff)   = Eff (S.map (subst $@) eff)

instance Substitute' Eff where
    Subst' ev $*@ (EffUnif u) | Just eff' <- M.lookup u ev = eff'
                              | otherwise                  = Eff (S.singleton (EffVar ("X" ++ u))) --error "non-covering substitution" -- FIXME: this case shoudn't be reached
    Subst' ev $*@ (Eff eff) = Eff (flattenSetOfSets (S.map f eff))
      where f (EffVar u) | Just (Eff eff') <- M.lookup u ev = eff'
                         | otherwise = S.singleton (EffVar u)
            f  EffCrash  = S.singleton EffCrash

instance Substitute Constr' where
    subst $@ k@(u :>: eff) = let Eff eff' = subst $@ (Eff eff)
                              in (subst $@ u) :>: eff'

instance Substitute Constr where
    subst $@ k = S.map (subst $@) k

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
    = Subst M.empty (M.singleton u1 u2)
unify' _ _
    = error "cannot unify effects"

-- | Inference

infer :: TyEnv -> Expr -> State [Ident] (Ty, Eff, Subst, Constr)
infer env (Var x)
    | Just (t, eff, k) <- M.lookup x env = return (t, eff, idSubst, k)
    | otherwise                          = error "variable not in scope"
infer env (Con c)
    = do u <- fresh
         case c of
            Bool _ -> return (TyCon TyBool, u, idSubst, S.empty)
            Int  _ -> return (TyCon TyInt , u, idSubst, S.empty)
infer env (Abs x e0)
    = do a <- fresh
         u <- fresh
         (t0, eff0, subst0, k0) <- infer (M.insert x (a, u, S.empty) env) e0
         u' <- fresh
         return (TyFun (subst0 $@ a) (subst0 $@ u) t0 eff0, u', subst0, k0)
infer env (App e1 e2)
    = do (t1, eff1, subst1, k1) <- infer            env  e1
         (t2, eff2, subst2, k2) <- infer (subst1 $@ env) e2
         a <- fresh
         u <- fresh
         let subst3 = unify (subst2 $@ t1) (TyFun t2 eff2 a u)
         u' <- fresh
         return ( subst3 $@ a, EffUnif u', subst3 $. subst2 $. subst1
                , S.singleton (u' :>: effect [subst3 $@ u, subst3 $@ (subst2 $@ eff1)])
                  `S.union` (subst3 $@ k2) `S.union` (subst3 $@ (subst2 $@ k1)))
infer env (Let x e1 e2)
    = do (t1, eff1, subst1, k1) <- infer                                       env   e1
         (t2, eff2, subst2, k2) <- infer (M.insert x (t1, eff1, k1) (subst1 $@ env)) e2
         return (t2, eff2, subst2 $. subst1, k2 `S.union` (subst2 $@ k1))
infer env Crash
    = do a <- fresh
         u <- fresh
         return (a, EffUnif u, idSubst, S.singleton (u :>: S.singleton EffCrash))

-- | Constraint solver (Talpin and Jouvelot style)

bar :: Constr -> Subst'
bar = S.foldr (\(u :>: eff) r -> Subst' (M.singleton u (r $*@ (Eff (S.singleton (EffVar u) `S.union` eff)))) $*. r) idSubst'
