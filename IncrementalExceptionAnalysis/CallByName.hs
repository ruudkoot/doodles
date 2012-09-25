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
    latex (TyFun t1 eff1 t2 eff2) = "\\left("
                                    ++ latex t1
                                    ++ "@"
                                    ++ latex eff1
                                    ++ "\\rightarrow "
                                    ++ latex t2
                                    ++ "@"
                                    ++ latex eff2
                                    ++ "\\right)"

-- | Environments

type TyEnv = M.Map Ident (Ty, Eff)

-- | Substitutions

infixr 0 $@
infixr 0 $*@
infixr 9 $.
infixr 9 $*.

data SimpleSubst = SimpleSubst (M.Map Ident Ty) (M.Map Ident Ident)
data AnnSubst    = AnnSubst    (M.Map Ident Eff)

idSimpleSubst :: SimpleSubst
idSimpleSubst = SimpleSubst M.empty M.empty

idAnnSubst :: AnnSubst
idAnnSubst = AnnSubst M.empty

($.) :: SimpleSubst -> SimpleSubst -> SimpleSubst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (SimpleSubst tv1 ev1) (SimpleSubst tv2 ev2)
            = SimpleSubst (M.unionWith (error "domains not distinct") tv1 tv2)
                          (M.unionWith (error "domains not distinct") ev1 ev2)

($*.) :: AnnSubst -> AnnSubst -> AnnSubst
s2 $*. s1 = (s2 $*@ s1) `substUnion` s2
    where 
        substUnion (AnnSubst ev1) (AnnSubst ev2)
            = AnnSubst (M.unionWith (error "domains not distinct") ev1 ev2)

instance LaTeX SimpleSubst where
    latex (SimpleSubst tv ev)
        | M.null tv && M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ mapsto "\\widehat\\tau" "" tv ++ "; "
                      ++ mapsto "\\dot\\varphi" "\\dot\\varphi" ev ++ "\\right]"

instance LaTeX AnnSubst where
    latex (AnnSubst ev)
        | M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ mapsto "\\dot\\varphi" "" ev ++ "\\right]"

class Substitute t where
    ($@) :: SimpleSubst -> t -> t

class Substitute' t where
    ($*@) :: AnnSubst -> t -> t

instance Substitute SimpleSubst where
    subst $@ (SimpleSubst tv ev)
        = SimpleSubst (M.map (subst $@) tv) (M.map (subst $@) ev)
     
instance Substitute' AnnSubst where
    subst $*@ (AnnSubst ev)
        = AnnSubst (M.map (subst $*@) ev)

instance Substitute Ty where
    SimpleSubst tv _ $@ (TyVar a)
        | Just t <- M.lookup a tv = t
    subst            $@ (TyFun t eff t' eff')
        = TyFun (subst $@ t) (subst $@ eff) (subst $@ t') (subst $@ eff')
    _                $@ x
        = x
        
instance Substitute' Ty where
    subst $*@ TyFun t eff t' eff'
        = TyFun (subst $*@ t) (subst $*@ eff) (subst $*@ t') (subst $*@ eff')
    _     $*@ x
        = x

instance Substitute TyEnv where
    subst $@ env = M.map (\(t, eff) -> (subst $@ t, subst $@ eff)) env

instance Substitute' TyEnv where -- needed to reconstruct the derivation tree
    subst $*@ env = M.map (\(t, eff) -> (subst $*@ t, subst $*@ eff)) env

instance Substitute Eff' where
    SimpleSubst _ ev $@ (EffVar v) | Just u <- M.lookup v ev = EffVar u
    _                $@ x          = x

instance Substitute Ident where
    -- FIXME: the identifiers are assumed to be from EffUnif
    SimpleSubst _ ev $@ u | Just u' <- M.lookup u ev = u'
                          | otherwise                = u

instance Substitute Eff where
    SimpleSubst _ ev $@ (EffUnif u) | Just eff' <- M.lookup u ev = EffUnif eff'
                                    | otherwise                  = EffUnif u
    subst      $@ (Eff eff)         = Eff (S.map (subst $@) eff)

instance Substitute' Eff where
    AnnSubst ev $*@ (Eff eff) = Eff (flattenSetOfSets (S.map f eff))
        where f (EffVar u) | Just (Eff eff') <- M.lookup u ev = eff'
                           | otherwise = S.singleton (EffVar u)
              f  EffCrash  = S.singleton EffCrash
    -- When applying kbar to eff
    AnnSubst ev $*@ (EffUnif u) | Just eff' <- M.lookup u ev = eff'
                                -- FIXME: should the following case be reachable?
                                | otherwise                  = Eff S.empty 

instance Substitute Constr' where
    subst $@ k@(u :>: eff) = let Eff eff' = subst $@ Eff eff
                              in (subst $@ u) :>: eff'

instance Substitute Constr where
    subst $@ k = S.map (subst $@) k

-- | Unification

unify :: Ty -> Ty -> SimpleSubst
unify (TyCon c1) (TyCon c2)
    | c1 == c2 = idSimpleSubst
unify (TyVar a) (TyVar a')
    = SimpleSubst (M.singleton a (TyVar a')) M.empty
unify (TyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = SimpleSubst (M.singleton a t) M.empty
unify t (TyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = SimpleSubst (M.singleton a t) M.empty
unify (TyFun t1 eff1 t2 eff2) (TyFun t1' eff1' t2' eff2')
    = let s1 = unify' (                  eff1) (                  eff1')
          s2 = unify' (            s1 $@ eff2) (            s1 $@ eff2')
          s3 = unify  (      s2 $@ s1 $@ t1  ) (      s2 $@ s1 $@ t1'  )
          s4 = unify  (s3 $@ s2 $@ s1 $@ t2  ) (s3 $@ s2 $@ s1 $@ t2'  )
       in s4 $. s3 $. s2 $. s1
unify _ _
    = error "constructor clash"

unify' :: Eff -> Eff -> SimpleSubst
unify' (EffUnif u1) (EffUnif u2)
    = SimpleSubst M.empty (M.singleton u1 u2)
unify' _ _
    = error "not a simple type"

-- | Inference

infer :: TyEnv -> Expr -> State ([Ident], InferenceTree Rule) (Ty, Eff, SimpleSubst, Constr)
infer env e@(Var x)
    | Just (t, eff) <- M.lookup x env = do putRule (Rule env e t eff)
                                           return (t, eff, idSimpleSubst, S.empty)
    | otherwise                       = error "variable not in scope"
infer env e@(Con c)
    = do u <- fresh
         case c of
            Bool _ -> do putRule (Rule env e (TyCon TyBool) u)
                         return (TyCon TyBool, u, idSimpleSubst, S.empty)
            Int  _ -> do putRule (Rule env e (TyCon TyInt ) u)
                         return (TyCon TyInt , u, idSimpleSubst, S.empty)
infer env e@(Abs x e0)
    = do a <- fresh
         u <- fresh
         down
         (t0, eff0, subst0, k0) <- infer (M.insert x (a, u) env) e0
         up
         u' <- fresh
         putRule (Rule env e (TyFun (subst0 $@ a) (subst0 $@ u) t0 eff0) u')
         return (TyFun (subst0 $@ a) (subst0 $@ u) t0 eff0, u', subst0, k0)
infer env e@(App e1 e2)
    = do down
         (t1, eff1, subst1, k1) <- infer            env  e1
         (t2, eff2, subst2, k2) <- infer (subst1 $@ env) e2
         up
         a <- fresh
         u <- fresh
         let subst3 = unify (subst2 $@ t1) (TyFun t2 eff2 a u)
         u' <- fresh
         putRule (Rule env e (subst3 $@ a) (EffUnif u'))
         return ( subst3 $@ a, EffUnif u', subst3 $. subst2 $. subst1
                , S.singleton (u' :>: effect [ subst3 $@ u
                                             , subst3 $@ subst2 $@ eff1 ])
                  `S.union` (subst3 $@ k2) `S.union` (subst3 $@ subst2 $@ k1))
infer env e@(Let x e1 e2)
    = do down
         (t1, eff1, subst1, k1) <- infer                                   env   e1
         (t2, eff2, subst2, k2) <- infer (M.insert x (t1, eff1) (subst1 $@ env)) e2
         up
         putRule (Rule env e t2 eff2)
         return (t2, eff2, subst2 $. subst1, k2 `S.union` (subst2 $@ k1))
infer env e@Crash
    = do a <- fresh
         u <- fresh
         putRule (Rule env e a (EffUnif u))
         return (a, EffUnif u, idSimpleSubst, S.singleton (u :>: S.singleton EffCrash))

-- | Typing rules

data Rule = Rule TyEnv Expr Ty Eff deriving Show

instance Substitute Rule where
    subst $@ (Rule env e t eff) = Rule (subst $@ env) e (subst $@ t) (subst $@ eff)

instance Substitute' Rule where
    subst $*@ (Rule env e t eff) = Rule (subst $*@ env) e (subst $*@ t) (subst $*@ eff)

instance LaTeX Rule where
    latex (Rule env e t eff)  = latex env
                                ++ " \\vdash "
                                ++ latex e
                                ++ " : "
                                ++ latex t
                                ++ "\\ \\&\\ "
                                ++ latex eff

-- | Constraint solver (Talpin and Jouvelot style)

bar :: Constr -> AnnSubst
bar = S.foldr (\(u :>: eff) r -> AnnSubst (M.singleton u (r $*@ Eff (S.singleton (EffVar u) `S.union` eff))) $*. r) idAnnSubst
