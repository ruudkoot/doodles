{-# LANGUAGE NoMonomorphismRestriction, TypeFamilies #-}

-- TODO: consider using strict and unboxed functions where possible
-- TODO: instrumented versions of the monads
-- TODO: automatic visualization based on the instrumentation

module Monad.Imperative (
    Ix(..),
    MonadImperative(..),
    skip,
    for,
    while,
    swapA
) where

import Control.Monad
import Control.Monad.ST
import Data.IORef
import Data.STRef
import Data.Array.IO
import Data.Array.ST

-- | Abstract over IO and ST monads

class Monad m => MonadImperative m where
    data Array m i e
    data Ref   m a
    newR    ::         a                     -> m (Ref m a)
    readR   ::         Ref m a               -> m a
    writeR  ::         Ref m a -> a          -> m ()
    modifyR ::         Ref m a -> (a -> a)   -> m ()
    readA   :: Ix i => Array m i e -> i      -> m e
    writeA  :: Ix i => Array m i e -> i -> e -> m ()
    
instance MonadImperative IO where
    data Array IO i e = IOArray { ioArray :: IOArray i e }
    data Ref   IO a   = IORef   { ioRef   :: IORef   a   }
    newR        x = newIORef               x >>= return . IORef
    readR   r     = readIORef   (ioRef   r)
    writeR  r   x = writeIORef  (ioRef   r) x
    modifyR r   f = modifyIORef (ioRef   r) f
    readA   a i   = readArray   (ioArray a) i
    writeA  a i e = writeArray  (ioArray a) i e
    
instance MonadImperative (ST s) where
    data Array (ST s) i e = STArray { stArray :: STArray s i e }
    data Ref   (ST s) a   = STRef   { stRef   :: STRef   s a   }
    newR        x = newSTRef               x >>= return . STRef
    readR   r     = readSTRef   (stRef   r)
    writeR  r   x = writeSTRef  (stRef   r)   x
    modifyR r   f = modifySTRef (stRef   r)   f
    readA   a i   = readArray   (stArray a) i
    writeA  a i e = writeArray  (stArray a) i e

-- | Control structures

-- * Skip

skip :: Monad m => m ()
skip = return ()

-- * While-loop

while :: Monad m => m Bool -> m () -> m ()
while g b = do
    p <- g
    if p then
        b >> while g b
    else
        return ()

-- * For-loop

for :: Monad m => m () -> m Bool -> m () -> m () -> m ()
for i g u b = i >> while g (b >> u)

-- | Arrays

swapA :: (MonadImperative m, Ix i, Ix j) => Array m i e -> i -> Array m j e -> j -> m ()
swapA a i b j = do
    x <- readA a i
    y <- readA b j
    writeA a i y
    writeA b j x
