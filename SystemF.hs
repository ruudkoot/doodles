{-# LANGUAGE RankNTypes #-}

module SystemF where

f1 :: a -> b
f1 = \x -> undefined

f2 :: (forall a. a) -> b
f2 = \x -> x
