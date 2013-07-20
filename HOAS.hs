{-# LANGUAGE GADTs, KindSignatures #-}

module Main where

data Lam :: * -> * where
  Lift :: a                     -> Lam a
  Tup  :: Lam a -> Lam b        -> Lam (a, b)
  Lam  :: (Lam a -> Lam b)      -> Lam (a -> b)
  App  :: Lam (a -> b) -> Lam a -> Lam b
  Fix  :: Lam (a -> a)          -> Lam a

eval :: Lam t -> t
eval (Lift v)    = v
eval (Tup e1 e2) = (eval e1, eval e2)
eval (Lam f)     = \x -> eval (f (Lift x))
eval (App e1 e2) = (eval e1) (eval e2)
eval (Fix f)     = (eval f) (eval (Fix f))

id' = App (Lam (\x -> Lam (\y -> App x y))) (Lift id)

f_ = \f y -> if y == 0 then 1 else y * f (y - 1)

fact = Fix (Lam (\f -> Lam (\y -> Lift (if eval y == 0 then 1 else eval y * (eval f) (eval y - 1)))))


