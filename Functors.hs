{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE ViewPatterns           #-}
{-# LANGUAGE InstanceSigs           #-}

-- functional dependencies --> associated types?
--     type classes --> records?
-- in-/nonvariance
-- other generalization directions: zip
-- arity-genericity: polyfunctors
-- generalize over co/contra/in/non
-- generalize to applicative, arrow, monad
-- arr to araity >2 (generalized categories?)

module Main where

-- | Abstact nonsense

-- * Opposite arrows

           -- why can't I use an opertor here?
newtype Op arr a b = Op { op :: b `arr` a }         -- FIXME: Op, Dual, or Flip?

type (:<-) = Op (->)

-- * More convenient names for co- and contravariance

type Co     = (->)
type Contra = (:<-)

-- | Variance-parameterized functors

class Functor' f p | f -> p where
    map :: p a b -> f a -> f b

instance Functor' [] Co where
    map = Prelude.map
    
-- | Variance-parameterized bifunctors

class Bifunctor f p q | f -> p, f -> q where
    bimap :: p a c -> q b d -> f a b -> f c d

{- functional dependencies can't handle this (i.c.w. the Category class below)
instance Bifunctor (,) Co Co where
    bimap :: (a -> c) -> (b -> d) -> (a , b) -> (c , d)
    bimap f g (x , y) = (f x , g y)
-}

instance Bifunctor (->) Contra Co where         -- "profunctor"
    bimap :: (a :<- c) -> (b -> d) -> (a -> b) -> (c -> d)
    bimap (op -> f) g h = g . h . f

-- | Categories

-- TODO: generalize the profunctor above to work over arbitrary categories
-- kind-polymorphism

                -- why can't I use an operator here?
class Category (arr :: * -> * -> *) where
    i :: a `arr` a                                  -- ^ reflexivity
    o :: b `arr` c -> a `arr` b -> a `arr` c        -- ^ transitivity
    
instance Category arr => Category (Op arr) where
    i       = Op i
    f `o` g = Op (op g `o` op f)                  -- this reeks of abstraction

instance Category (->) where
    i = id
    o = (.)

instance Category arr => Bifunctor arr (Op arr) arr where
    bimap (op -> f) g h = g `o` h `o` f

-- TODO: try on some non-trivial arrows
    
-- | Applicative functors

class Functor' f => Applicative' f where
    embed :: a -> f a
    

-- class Biapplicative where


-- class Coapplicative where

-- http://sneezy.cs.nott.ac.uk/fplunch/weblog/?p=69
-- http://www.reddit.com/r/haskell/comments/qsrmq/coapplicative_functor/

-- | Arrows

-- | Monads

-- class Bimonad where
-- class Comonad where
