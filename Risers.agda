module Risers where

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

data List : Set -> Set where
  Nil  : forall a.               List a
  Cons : forall a. a -> List a -> List a

risers : forall a. List a -> List (List a)
risers _ = Nil