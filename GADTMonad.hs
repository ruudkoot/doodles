{-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving #-}

module Main where

import Control.Monad

data GMaybe :: * -> * where
    GJust :: a -> GMaybe a
    GJustC :: (Show a) => a -> GMaybe a
    GNothing :: GMaybe a
    
deriving instance Show a => Show (GMaybe a)
    
instance Monad GMaybe where
    return x         = GJustC x
    GNothing   >>= _ = GNothing
    (GJust a)  >>= f = f a
    (GJustC a) >>= f = f a
    
test = do x <- f
          y <- g
          return 9
    where f = GJust 1
          g = GJustC 2
