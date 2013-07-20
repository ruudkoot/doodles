{-# LANGUAGE GADTs, KindSignatures, TypeFamilies, TypeOperators, RankNTypes #-}

module Main where

data (x :: *) :=: (y :: *) :: * where
    Refl :: x :=: x


data E :: * -> * where
    CInt       :: forall a.   (a ~ Int)  => a                 -> E a
    CBool      :: forall a.   (a ~ Bool) => a                 -> E a
    (:+:)      :: forall a.   (a ~ Int)  => E a -> E a        -> E a
    IfThenElse :: forall a b. (b ~ Bool) => E b -> E a -> E a -> E a

