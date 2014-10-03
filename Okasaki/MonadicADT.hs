{-# LANGUAGE NoMonomorphismRestriction, NoImplicitPrelude #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances     #-}

module Main where

import Prelude (Bool)
import Control.Monad.Parameterized

-- * "Monadic" ADTs

-- Some data structures will return a new version after query operations
-- (e.g. splay trees), these might be more conveniently handles in monadic
-- style than purely functional.
--
-- Such a monad might also want to handle any failures.

{-
class Monad m => MonadMonoid m a where
    empty :: m a
    null  :: m Bool
    (++)  :: a -> a -> m a
-}

class MonadZero m => MonadDeque m f a where
    empty :: m ()
    cons  :: a -> m ()
    head  ::      m a
    tail  ::      m ()
    snoc  :: a -> m ()
    last  ::      m ()
    init  ::      m ()



-- MonadState + Maybe ---> MonadZeroState

-- imperative variables are indices into a State record
--   \--> lenses?



-- | Monoids 


class Unital a where
    empty :: a

class Magma a where
    (++) :: a -> a -> a

class Magma a => Semigroup a

class (Unital a, Magma a) => Monoid a


foo = do
    x <- new
    y <- new
    
    
-- build up an appropriate state monad a la "datatypes a la carte"
