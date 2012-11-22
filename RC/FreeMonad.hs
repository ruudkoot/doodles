{-# LANGUAGE FlexibleContexts, StandaloneDeriving, UndecidableInstances #-}

module FreeMonad where

import Data.Tree

data FreeMonad p x = V x | C (p (FreeMonad p x))

deriving instance (Eq   x, Eq   (p x), Eq   (p (FreeMonad p x))) => Eq   (FreeMonad p x)
deriving instance (Ord  x, Ord  (p x), Ord  (p (FreeMonad p x))) => Ord  (FreeMonad p x)
deriving instance (Show x, Show (p x), Show (p (FreeMonad p x))) => Show (FreeMonad p x)

ex1 :: FreeMonad [] String
ex1 = C [C [V "a", V "b"], V "c", C []]

instance Functor p => Monad (FreeMonad p) where
    return x = V x
    V x >>= s = s x
    C pt >>= s = C (fmap (>>= s) pt)
    
test1 :: FreeMonad [] String
test1 = do x <- return "a"
           y <- return "b"
           V "c"
           ex1
           C [V "v", V "w"]

d :: Functor p => FreeMonad p (Maybe x) -> FreeMonad p x -> FreeMonad p x
t `d` s = t >>= sigma where
    sigma Nothing = s
    sigma (Just x) = V x
