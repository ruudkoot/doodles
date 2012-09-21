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

data Ty
    = TyVar Ident
    | TyCon TyCon
    | TyFun Ty Eff Ty
    deriving (Eq, Ord, Show)
    
instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar a)

instance FreeVars Ty where
    ftv (TyCon _     ) = S.empty
    ftv (TyFun t _ t') = ftv t `S.union` ftv t'
    ftv (TyVar a     ) = S.singleton a

instance LaTeX Ty where
    latex (TyVar a        ) = "\\widehat\\tau" ++ a
    latex (TyCon TyBool   ) = "\\mathbf{Bool}"
    latex (TyCon TyInt    ) = "\\mathbf{Int}"
    latex (TyFun t1 eff t2) = "\\left(" ++ latex t1
                              ++ "\\xrightarrow{" ++ latex eff ++ "}"
                              ++ latex t2 ++ "\\right)"

-- | Environments

type TyEnv = M.Map Ident Ty

-- | Substitutions

infixr 0 $@
infixr 0 $*@
infixr 9 $.
infixr 9 $*.

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
            = Subst (M.unionWith (error "domains not distinct") tv1 tv2)
                    (M.unionWith (error "domains not distinct") ev1 ev2)

($*.) :: Subst' -> Subst' -> Subst'
s2 $*. s1 = (s2 $*@ s1) `substUnion` s2
    where 
        substUnion (Subst' ev1) (Subst' ev2)
            = Subst' (M.unionWith (error "domains not distinct") ev1 ev2)

instance LaTeX Subst where
    latex (Subst tv ev)
        | M.null tv && M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ mapsto "\\widehat\\tau" "" tv ++ "; "
                      ++ mapsto "\\dot\\varphi" "\\dot\\varphi" ev ++ "\\right]"

instance LaTeX Subst' where
    latex (Subst' ev)
        | M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ mapsto "\\dot\\varphi" "" ev ++ "\\right]"

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
    subst      $@ (TyFun t eff t')
        = TyFun (subst $@ t) (subst $@ eff) (subst $@ t')
    _          $@ x
        = x

instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env
    
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
    Subst' ev $*@ (Eff eff) = Eff (flattenSetOfSets (S.map f eff))
        where f (EffVar u) | Just (Eff eff') <- M.lookup u ev = eff'
                           | otherwise = S.singleton (EffVar u)
              f  EffCrash  = S.singleton EffCrash
    -- When applying kbar to eff
    Subst' ev $*@ (EffUnif u) | Just eff' <- M.lookup u ev = eff'
                              | otherwise                  = error "non-covering substitution"

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
unify (TyFun t1 eff t2) (TyFun t1' eff' t2')
    = let subst1 = unify' (                    eff) (eff'                   )  
          subst2 = unify  (          subst1 $@ t1 ) (          subst1 $@ t1')
          subst3 = unify  (subst2 $@ subst1 $@ t2 ) (subst2 $@ subst1 $@ t2')
       in subst3 $. subst2 $. subst1
unify _ _
    = error "constructor clash"

unify' :: Eff -> Eff -> Subst
unify' (EffUnif u1) (EffUnif u2)
    = Subst M.empty (M.singleton u1 u2)
unify' _ _
    = error "not a simple type"

-- | Inference

infer :: TyEnv -> Expr -> State [Ident] (Ty, Eff, Subst, Constr)
infer env (Var x)
    | Just t <- M.lookup x env = do u <- fresh
                                    return (t, EffUnif u, idSubst, S.empty)
    | otherwise                = error "variable not in scope"
infer env (Con c)
    = do u <- fresh
         case c of
            Bool _ -> return (TyCon TyBool, u, idSubst, S.empty)
            Int  _ -> return (TyCon TyInt , u, idSubst, S.empty)
infer env (Abs x e0)
    = do a <- fresh
         (t0, eff0, subst0, k0) <- infer (M.insert x a env) e0
         u' <- fresh
         return (TyFun (subst0 $@ a) eff0 t0, u', subst0, k0)
infer env (App e1 e2)
    = do (t1, eff1, subst1, k1) <- infer            env  e1
         (t2, eff2, subst2, k2) <- infer (subst1 $@ env) e2
         a <- fresh
         u <- fresh
         let subst3 = unify (subst2 $@ t1) (TyFun t2 u a)
         u' <- fresh
         return ( subst3 $@ a, EffUnif u', subst3 $. subst2 $. subst1
                , S.singleton (u' :>: effect [ subst3 $@ u
                                             , subst3 $@ (subst2 $@ eff1)
                                             , subst3 $@            eff2 ])
                  `S.union` (subst3 $@ subst2 $@ k1) `S.union` (subst3 $@ k2) )
infer env (If e0 e1 e2)
    = do (t0, eff0, subst0, k0) <- infer env e0
         (t1, eff1, subst1, k1) <- infer (subst0 $@ env) e1
         (t2, eff2, subst2, k2) <- infer (subst1 $@ subst0 #@ env) e2
         let subst3 = unify (subst2 $@ subst1 $@ t0) (TyCon TyBool)
infer env (Let x e1 e2)
    = do (t1, eff1, subst1, k1) <- infer                           env   e1
         (t2, eff2, subst2, k2) <- infer (M.insert x t1 (subst1 $@ env)) e2
         u <- fresh
         return ( t2, EffUnif u, subst2 $. subst1
                , S.singleton (u :>: effect [subst2 $@ eff1, eff2])
                 `S.union` (subst2 $@ k1) `S.union` k2              )
infer env Crash
    = do a <- fresh
         u <- fresh
         return (a, EffUnif u, idSubst, S.singleton (u :>: S.singleton EffCrash))
         
-- | Constraint solver (Talpin and Jouvelot style)

bar :: Constr -> Subst'
bar = S.foldr (\(u :>: eff) r -> Subst' (M.singleton u (r $*@ (Eff (S.singleton (EffVar u) `S.union` eff)))) $*. r) idSubst'
