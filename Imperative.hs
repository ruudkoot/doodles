{-# LANGUAGE NoMonomorphismRestriction, TypeFamilies #-}

module Imperative where

import Prelude hiding (read)

import Control.Monad
import Control.Monad.ST
import Data.STRef
import Data.IORef
import Data.Array.IO
import Data.Array.ST

-- | Abstract over IO and ST monads

class Monad m => MonadImperative m where
    data Array m i e
    data Ref   m a
    new    :: a -> m (Ref m a)
    read   :: Ref m a -> m a
    write  :: Ref m a -> a -> m ()
    modify :: Ref m a -> (a -> a) -> m ()
    
(<<-) :: MonadImperative m => Ref m a -> m a -> m ()
r <<- m = do
    m' <- m
    write r m'
    
infix 0 <<-

instance MonadImperative IO where
    data Array IO i e = IOArray { ioArray :: IOUArray i e }
    data Ref   IO a   = IORef { ioRef :: IORef    a   }
    new      x = newIORef               x >>= return . IORef
    read   r   = readIORef    (ioRef r)
    write  r x = writeIORef   (ioRef r) x
    modify r f = modifyIORef' (ioRef r) f
    
instance MonadImperative (ST s) where
    data Array (ST s) i e = STArray { stArray :: STUArray s i e }
    data Ref   (ST s) a   = STRef { stRef :: STRef    s a }
    new      x = newSTRef               x >>= return . STRef
    read   r   = readSTRef    (stRef r)
    write  r x = writeSTRef   (stRef r) x
    modify r f = modifySTRef' (stRef r) f

-- | Control structures

-- * While-loop

while :: Monad m => m Bool -> m () -> m ()
while g b = do
    p <- g
    if p then
        b >> while g b
    else
        return ()

-- * For-loop

for' :: Monad m => m () -> m Bool -> m () -> m () -> m ()
for' i g u b = i >> while g (b >> u)

data SYNTAX

from, to :: SYNTAX
from = error "from"
to   = error "to"

for :: (Enum a, Ord a, MonadImperative m) => Ref m a -> SYNTAX -> a -> SYNTAX -> m a -> m () -> m ()
for i _ p _ q b = for' (write i p) f (modify i succ) b
    where f = do i' <- read i
                 q' <- q
                 return (i' <= q')

-- | Operators

(>) :: MonadImperative m => Ref m Int -> Int -> m Bool
(>) = undefined

infix 4 >

(&&) :: MonadImperative m => m Bool -> m Bool -> m Bool
(&&) = undefined

infixr 3 &&

(+) :: MonadImperative m => Ref m Int -> Int -> m Int
(+) = undefined

infixl 7 +

(-) :: MonadImperative m => Ref m Int -> Int -> m Int
(-) = undefined

infixl 7 -

-- | Arrays

type Arr m e = Ref m Int -> m e

length :: MonadImperative m => Arr m e -> m Int
length = undefined

set :: MonadImperative m => Arr m e -> m Int -> Arr m e -> m Int -> m ()
set = undefined

set' :: MonadImperative m => Arr m e -> m Int -> Int -> m ()
set' = undefined

-- | Initializers

int :: Int
int = 0
