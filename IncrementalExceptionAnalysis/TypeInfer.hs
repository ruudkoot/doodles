{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module TypeInfer where

import Control.Monad
import Control.Monad.State

import qualified Data.Map as M
import qualified Data.Set as S

import Fresh
import Printing

import Syntax
import Analysis

-- | Types

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

-- | Free variables

instance FreeVars Ty where
    ftv (TyCon _   ) = S.empty
    ftv (TyFun t t') = ftv t `S.union` ftv t'
    ftv (TyVar a   ) = S.singleton a

-- | Substitutions

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

-- | Unification

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

-- | Type inference

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
