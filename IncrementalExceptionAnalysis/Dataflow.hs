{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Dataflow where

import Control.Monad
import Control.Monad.State

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S

import Fresh
import Printing
import Util

import Syntax
import Analysis hiding (TyCon(..), Constr, Constr'(..))

-- | Annotated types

data TyCon
    = TyBool Ref
    | TyInt  Ref
    deriving (Eq, Ord, Show)

data Ref
    = RefUnif Ident
    | RefBool (S.Set (VC Bool))
    | RefInt  (S.Set (VC Int'))
    deriving (Eq, Ord, Show)

data VC t
    = RefVar Ident
    | RefCon t
    deriving (Eq, Ord, Show)

data Int' = Neg | Zero | Pos deriving (Eq, Ord, Show)

inject :: Int -> Int'
inject n | n <  0 = Neg
         | n == 0 = Zero
         | n >  0 = Pos

data Ty
    = TyVar Ident
    | TyCon TyCon
    | TyFun Ty Ty
    deriving (Eq, Ord, Show)

instance Fresh Ref where
    fresh = do r <- fresh
               return (RefUnif r)

instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar a)
            
instance FreeVars Ty where
    ftv (TyVar a    ) = S.singleton a
    ftv (TyCon _    ) = S.empty
    ftv (TyFun t1 t2) = ftv t1 `S.union` ftv t2
    
instance LaTeX Ty where
    latex (TyVar a         ) = "\\widehat\\tau" ++ a
    latex (TyCon (TyBool r)) = "\\mathbf{Bool}" ++ "^{" ++ latex r ++ "}"
    latex (TyCon (TyInt  r)) = "\\mathbf{Int}"  ++ "^{" ++ latex r ++ "}"
    latex (TyFun t1 t2     ) = "\\left("
                               ++ latex t1
                               ++ "\\rightarrow"
                               ++ latex t2
                               ++ "\\right)"

instance LaTeX Ref where
    latex (RefUnif u) = "\\dot\\rho" ++ u
    latex (RefBool s) = latex s
    latex (RefInt  s) = latex s

instance LaTeX t => LaTeX (VC t) where
    latex (RefVar r) = "\\rho" ++ r
    latex (RefCon r) = latex r    

instance LaTeX Int' where
    latex s = "\\mathbf{" ++ show s ++ "}"

-- | Environments 

type TyEnv = M.Map Ident Ty

-- | Constraints

data Constr'
    = Ident :>: Ref
    deriving (Eq, Ord, Show)
    
type Constr = S.Set Constr'

instance LaTeX Constr' where
    latex (u :>: ref) = "\\dot\\rho" ++ u ++ "\\supseteq" ++ latex ref

-- | Substitutions

infixr 0 $@
infixr 0 $*@
infixr 9 $.
infixr 9 $*.

data SimpleSubst = SimpleSubst (M.Map Ident Ty) (M.Map Ident Ident)
data RefSubst    = RefSubst    (M.Map Ident Ref)

idSimpleSubst :: SimpleSubst
idSimpleSubst = SimpleSubst M.empty M.empty

idRefSubst :: RefSubst
idRefSubst = RefSubst M.empty

($.) :: SimpleSubst -> SimpleSubst -> SimpleSubst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (SimpleSubst tv1 ev1) (SimpleSubst tv2 ev2)
            = SimpleSubst (M.unionWith (error "domains not distinct") tv1 tv2)
                          (M.unionWith (error "domains not distinct") ev1 ev2)

($*.) :: RefSubst -> RefSubst -> RefSubst
s2 $*. s1 = (s2 $*@ s1) `substUnion` s2
    where 
        substUnion (RefSubst ev1) (RefSubst ev2)
            = RefSubst (M.unionWith (error "domains not distinct") ev1 ev2)

instance LaTeX SimpleSubst where
    latex (SimpleSubst tv ev)
        | M.null tv && M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ mapsto "\\widehat\\tau" "" tv ++ "; "
                      ++ mapsto "\\dot\\varphi" "\\dot\\varphi" ev ++ "\\right]"

instance LaTeX RefSubst where
    latex (RefSubst ev)
        | M.null ev = "\\epsilon"
        | otherwise = "\\left[" ++ mapsto "\\dot\\varphi" "" ev ++ "\\right]"

class Substitute t where
    ($@) :: SimpleSubst -> t -> t

class Substitute' t where
    ($*@) :: RefSubst -> t -> t

instance Substitute SimpleSubst where
    subst $@ (SimpleSubst tv ev)
        = SimpleSubst (M.map (subst $@) tv) (M.map (subst $@) ev)
     
instance Substitute' RefSubst where
    subst $*@ (RefSubst ev)
        = RefSubst (M.map (subst $*@) ev)

instance Substitute Ty where
    SimpleSubst tv _ $@ (TyVar a)
        | Just t <- M.lookup a tv = t
    subst            $@ (TyFun t t')
        = TyFun (subst $@ t) (subst $@ t')
    _                $@ x
        = x
        
instance Substitute' Ty where
    subst $*@ TyFun t t'
        = TyFun (subst $*@ t) (subst $*@ t')
    _     $*@ x
        = x

instance Substitute TyEnv where
    subst $@ env = M.map (\t -> subst $@ t) env

instance Substitute' TyEnv where
    subst $*@ env = M.map (\t -> subst $*@ t) env

instance Substitute Ident where
    -- FIXME: the identifiers are assumed to be from EffUnif
    SimpleSubst _ ev $@ u | Just u' <- M.lookup u ev = u'
                          | otherwise                = u

instance Substitute (VC t) where
    subst $@ (RefVar u) = RefVar (subst $@ u)
    subst $@ x          = x

instance Substitute Ref where
    SimpleSubst _ rv $@ (RefUnif u) | Just u' <- M.lookup u rv = RefUnif u'
                                    | otherwise                = RefUnif u
    subst            $@ (RefBool r) = RefBool (S.map (subst $@) r)
    subst            $@ (RefInt  r) = RefInt  (S.map (subst $@) r)

instance Substitute' Ref where
    RefSubst rv $*@ (RefBool ref) = RefBool (flattenSetOfSets (S.map f ref))
        where f (RefVar r) | Just (RefBool ref') <- M.lookup r rv = ref'
                           | otherwise = S.singleton (RefVar r)
    RefSubst rv $*@ (RefInt  ref) = RefInt  (flattenSetOfSets (S.map f ref))
        where f (RefVar r) | Just (RefInt  ref') <- M.lookup r rv = ref'
                           | otherwise = S.singleton (RefVar r)
    -- FIXME: need a case for RefUnif when applying kbar to ref

instance Substitute Constr' where
    subst $@ (u :>: ref) = (subst $@ u) :>: (subst $@ ref)

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
unify (TyFun t1 t2) (TyFun t1' t2')
    = let s1 = unify  (      t1) (      t1')
          s2 = unify  (s1 $@ t2) (s1 $@ t2')
       in s2 $. s1
unify _ _
    = error "constructor clash"

unify' :: Ref -> Ref -> SimpleSubst
unify' (RefUnif u1) (RefUnif u2)
    = SimpleSubst M.empty (M.singleton u1 u2)
unify' _ _
    = error "not a simple type"
    
-- | Inference

infer :: TyEnv -> Expr -> State ([Ident], InferenceTree ()) (Ty, SimpleSubst, Constr)
infer env (Var x)
    | Just t <- M.lookup x env = return (t, idSimpleSubst, S.empty)
    | otherwise                = error "variable not in scope"
infer env (Con c)
    = do u <- fresh
         case c of
            Bool b -> return ( TyCon (TyBool (RefUnif u)), idSimpleSubst
                             , S.singleton (u :>: RefBool (S.singleton (RefCon b))) )
            Int  n -> return ( TyCon (TyInt  (RefUnif u)), idSimpleSubst
                             , S.singleton (u :>: RefInt (S.singleton (RefCon (inject n)))) )
infer env (Abs x e0)
    = do a <- fresh
         (t0, subst0, k0) <- infer (M.insert x a env) e0
         return (TyFun (subst0 $@ a) t0, subst0, k0)
infer env (App e1 e2)
    = do (t1, subst1, k1) <- infer            env  e1
         (t2, subst2, k2) <- infer (subst1 $@ env) e2
         a <- fresh
         let subst3 = unify (subst2 $@ t1) (TyFun t2 a)
         return (subst3 $@ a, subst3 $. subst2 $. subst1, k2 `S.union` (subst2 $@ k1))
infer env (Let x e1 e2)
    = do (t1, subst1, k1) <- infer env e1
         (t2, subst2, k2) <- infer (M.insert x t1 (subst1 $@ env)) e2
         return (t2, subst2 $. subst1, k2 `S.union` (subst2 $@ k1))
infer env (If e0 e1 e2)
    = do (t0, subst0, k0) <- infer env e0
         (t1, subst1, k1) <- infer (subst0 $@ env) e1
         (t2, subst2, k2) <- infer (subst1 $@ subst0 $@ env) e2
         r <- fresh
         let subst3 = unify (subst2 $@ subst3 $@ t0) (TyCon (TyBool r))
         let subst4 = unify (subst3 $@ subst2 $@ t1) (subst3 $@ t2)
         return ( subst4 $@ subst3 $@ t2
                , subst4 $. subst3 $. subst2 $. subst1 $. subst0
                , (subst4 $@ subst3 $@ k2)
                  `S.union` (subst4 $@ subst3 $@ subst2 $@ k2)
                  `S.union` (subst4 $@ subst3 $@ subst2 $@ subst1 $@ k0) )
