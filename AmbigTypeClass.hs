{-# LANGUAGE GADTs, KindSignatures, TypeFamilies, RankNTypes, MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables, NoMonomorphismRestriction, ConstraintKinds #-}

module Main where

class Foo a b where
    foo :: a -> b -> Int

instance Foo Int b
instance Foo a b => Foo [a] b

g :: forall b. (forall c. Foo b c) => b -> Int
g y = let h :: forall c. c -> Int
          h x = foo y x
       in h True
