{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Main where

import Control.Monad
import Control.Monad.State

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
    = Con c
cbn' env (Abs x e)
    = Close (Abs x e) env
cbn' env (App e1 e2)
    = case cbn' env e1 of
        Crash -> Crash
        Close (Abs x e1') env' -> cbn' (M.insert x (Close e2 env) env') e1'
        x -> error $ show x
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
    latex (TyVar a     ) = a
    latex (TyCon TyBool) = "\\mathbf{Bool}"
    latex (TyCon TyInt ) = "\\mathbf{Int}"
    latex (TyFun t1 t2 ) = "(" ++ latex t1 ++ "\\rightarrow" ++ latex t2 ++ ")"

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
    
-- * Type inference

type TyEnv = M.Map Ident Ty

instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env

infer :: TyEnv -> Expr -> State [Ident] (Ty, Subst)
infer env (Var x)
    = return (fromJust (M.lookup x env), idSubst)
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
    
-- * Free variables

class FreeVars t where
    ftv :: t -> S.Set Ident

instance FreeVars Ty where
    ftv (TyCon _   ) = S.empty
    ftv (TyFun t t') = ftv t `S.union` ftv t'
    ftv (TyVar a   ) = S.singleton a
    
-- | Examples

main
    = do putStrLn preamble
         example "Example 1" ex1
         example "Example 2" ex2
         example "Example 3" ex3
         putStrLn postamble
          
example name ex
    = do putStrLn ("\\paragraph{" ++ name ++ "}")
         putStrLn "\\begin{eqnarray}"
         putStrLn (latex ex ++ newline)
         let ((t, subst), _) = runState (infer M.empty ex3) freshIdents
         putStrLn (latex t ++ newline)
         putStrLn (latex (cbv ex) ++ newline)
         putStrLn (latex (cbn ex))
         putStrLn "\\end{eqnarray}"

ex1 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Int 3))) (Con (Bool False)))
ex2 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Bool True))) Crash)
ex3 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (Var "const")
ex4 = Let "id" (Abs "x" (Var "x")) (App (Var "id") (Var "id")) -- needs let-polymorphism
