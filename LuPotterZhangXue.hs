{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module LuPotterZhangXue where

import Control.Monad
import Control.Monad.State

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S
import qualified Data.Tree as T

-- | Syntax

type Name   = String

type Ident  = Name
type Label  = Name
type Region = S.Set Label

data Expr
    = Int Int
    | Fn Ident Expr
    | Var Ident
    | App Expr Expr
    | Ref Label Expr
    | Deref Expr
    | Expr := Expr
    | Fork Expr
    | Det Expr
    deriving (Eq, Ord, Show)
    
_let x e1 e2 = App (Fn x e2) e1
_seq   e1 e2 = _let "_" e1 e2

-- | Static semantics

data Ty
    = TyVar Name
    | TyInt
    | TyFun Ty DetEff Ty
    | TyRef Region Ty
    deriving (Eq, Ord, Show)

data Eff'
    = EffVar Name
    | EffDeref Region
    | EffAssign Region
    | EffFork Eff
    | EffDet Eff
    deriving (Eq, Ord, Show)
    
data Eff
    = EffUnif Name
    | Eff (S.Set Eff')
    deriving (Eq, Ord, Show)

data Lvl' = Weak | Non deriving (Eq, Ord, Show)

data Lvl
    = LvlVar Name
    | Lvl Lvl'
    deriving (Eq, Ord, Show)

type DetEff = (Eff, Lvl)

type TyEnv = M.Map Ident Ty

-- * Constraints

data Constr'
    = Eq DetEff DetEff
    | Seq DetEff DetDef DetEff
    deriving (Eq, Ord, Show)
    
type Constr = S.Set Constr'

-- * Inference

infer :: TyEnv -> Expr -> State ([Name], ()) (Ty, DetEff, Subst, Constr)
infer env (Int c)
    = do de <- fresh
         return (TyInt, de, idSubst, S.singleton (Eq (Eff S.empty, Lvl Weak) de))
infer env (Var x)
    | Just t <- M.lookup x env
        = return (t, (Eff S.empty, Lvl Weak), idSubst, S.empty)
    | otherwise = error "variable not in scope"
infer env (Fn x e)
    = do t2 <- fresh
         (t1, de1, subst1, k1) <- infer (M.insert x t2 env) 
         return (TyFun (subst1 $@ t2) de1 t1, de, subst1)
infer env (App e1 e2)
    = do (t1', de1, subst1) <- infer env e1
         (t2 , de2, subst2) <- infer (subst1 $@ env) e2
         t1 <- fresh
         e3 <- fresh
         d3 <- fresh
         let subst3 = unify (subst2 $@ t1') (TyFun t2 (e3, d3) t1)
         return 
         

-- | Examples

ex522a = _let "val" (Ref "pi" (Int 0)) (_let "set" (Fn "x" (Var "val" := Var "x"))
            ((Fork (App (Var "set") (Int 2))) `_seq` Deref (Var "val")))
ex522b = _let "val" (Ref "pi" (Int 0)) (_let "set" (Fn "x" (Var "val" := Var "x"))
            (Deref (Var "val") `_seq` (Fork (App (Var "set") (Int 2)))))
ex522c = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 0))
            (_let "f" (Fn "z" (Fork (Var "x" := Int 1 `_seq` Var "y" := Int 1)))
            (Var "x" := Int 2 `_seq` App (Var "f") (Int 0) `_seq` Var "y" := Int 2)))
ex523' = _let "x" (Ref "pi" (Int 1)) (_let "y" (Ref "varpi" (Int 2))
            (_let "lim" (Fn "z" (Deref (Var "z")))
            ((Fork (App (Var "lim") (Var "x")))
                `_seq` Fork (App (Var "lim") (Var "y"))
                `_seq` Fork (App (Var "lim") (Var "x")))))
ex524a = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 1))
            (Fork (Var "x" := Int 1)
                `_seq` Fork (Var "x" := Deref (Var "y"))
                `_seq` Det (Var "y" := Int 2)))
ex524b = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 1))
            (Fork (Var "x" := Int 1)
                `_seq` Fork (Var "x" := Deref (Var "y"))
                `_seq` Det (Var "y" := Deref (Var "x"))))
ex524c = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 1))
            (Det (Fork (Var "x" := Int 2))
                `_seq` (Var "y" := Deref (Var "x"))))
ex524d = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 1))
            (Det (Fork (Var "y" := Deref (Var "x")))
                `_seq` (Var "x" := Int 2)))
                
-- | Fresh identifiers

class Fresh a where 
    fresh :: State ([Name], s') a
    
instance Fresh Ident where
    fresh = do ((x:xs), s') <- get
               put (xs, s')
               return x
               
instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar a)
               
instance Fresh Eff where
    fresh = do u <- fresh 
               return (EffUnif u)
               
instance Fresh Lvl where
    fresh = do d <- fresh
               return (LvlVar d)
               
instance Fresh DetEff where
    fresh = do e <- fresh
               d <- fresh
               return (e, d)
               
freshIdents = map (\n -> "_{" ++ show n ++ "}") [1..]

-- | Substitutions

data Subst = Subst (M.Map Name Ty) (M.Map Name Name)

idSubst :: Subst
idSubst = Subst (M.empty) (M.empty)
