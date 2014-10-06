{-# LANGUAGE NoImplicitPrelude                         #-}
{-# LANGUAGE TypeFamilies, TypeOperators, ViewPatterns #-}

module Main where

-- | Prelude

undefined = undefined

-- | Functions

class IsFunction (arr :: * -> * -> *) where
    lambda :: (a -> b) -> a `arr` b
    (@@)   :: a `arr` b -> a -> b

instance IsFunction (->) where
    lambda = id
    f @@ x = f x
    
infixl 9 @@

-- | Categories

class Category arr where
    id :: a `arr` a
    (.) :: b `arr` c -> a `arr` b -> a `arr` c
    
instance Category (->) where
    id      x = x
    (f . g) x = f (g x)

{-
instance Category arr => Category (Op arr) where
    id x      = undefined
    (f . g) x = undefined
-}

-- | Opposites

newtype Op arr a b = Op { op :: b `arr` a }

type (<~) = Op (->)

-- | Bifunctors

type Covariant     = (->)
type Contravariant = (<~)

class Bifunctor (f :: * -> * -> *) where
    type Arg1 f :: * -> * -> *
    type Arg2 f :: * -> * -> *
    bimap :: Arg1 f a a' -> Arg2 f b b' -> f a b -> f a' b'

instance Bifunctor (,) where
    type Arg1 (,) = Covariant
    type Arg2 (,) = Covariant
    bimap f g (x , y) = (f x , g y)

instance Bifunctor (->) where
    type Arg1 (->) = Contravariant
    type Arg2 (->) = Covariant
    bimap (op -> i) o f = o . f . i

-- * boxed arrow

data (:->) a b = Arr { arr :: a -> b }

infixr 9 :->

-- {#- LANGUAGE OverloadedFunctions #-}
instance IsFunction (:->) where
    lambda          = Arr
    (arr -> f) @@ x = f x

instance Category (:->) where
    id                      = Arr id
    (arr -> f) . (arr -> g) = Arr (f . g)

instance Bifunctor (:->) where
    type Arg1 (:->) = Contravariant
    type Arg2 (:->) = Covariant
    bimap (op -> i) o (arr -> f) = Arr (o . f . i)

-- * "set-theoretic" functions

-- * stateful functions

-- * non-standard kinds
