{-# LANGUAGE RankNTypes #-}

module ASG4DSL3 where

-- | 3.  (Mutual) recursion

type ClosedExpr = forall a. Expr a

data Expr a
    = Lit Int
    | Add (Expr a) (Expr a)
    | IfZero (Expr a) (Expr a) (Expr a)
    | Var a
    | Let (Expr a) (a -> Expr a)
    | Lam (a -> Expr a)
    | App (Expr a) (Expr a)

(#)        = Add
(%)        = App
let_ e1 e2 = Let e1 (\x -> e2 (Var x))
lam_ e     = Lam (\x -> e (Var x))
