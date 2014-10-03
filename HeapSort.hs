module Main where

import Control.Monad
import Data.Array.IO
import Data.Array.MArray
import Data.IORef

type Ref   a = IORef       a
type Array e = IOArray Int e

newRef    = newIORef
readRef   = readIORef
(<<-)     = writeIORef
modifyRef = modifyIORef'

skip = return ()

-- | Heaps

type Heap e = (Array e, Int)

swap :: Heap e -> Int -> Int -> IO ()
swap a@(a',_) x y = do
    e <- a#x
    f <- a#y
    writeArray a' x f
    writeArray a' y e
    return ()

parent :: Int -> Int
parent i = i `div` 2

left :: Int -> Int
left i = 2 * i

right :: Int -> Int
right i = 2 * i + 1

heapSize :: Heap e -> Int
heapSize (_, n) = n

(#) :: Heap e -> Int -> IO e
(a, _) # n = readArray a n

maxHeapify :: Ord e => Heap e -> Int -> IO (Heap e)
maxHeapify a i = do
    let l = left  i
    let r = right i
    a_l     <- a#l
    a_i     <- a#i
    largest <- newRef 0
    if l <= heapSize a && a_l > a_i then do
        largest <<- l
    else do
        largest <<- i
    largest'  <- readRef largest
    a_r       <- a#r
    a_largest <- a#largest'
    if r <= heapSize a && a_r > a_largest then do
        largest <<- r
    else do
        skip
    largest' <- readRef largest
    if largest' /= i then do
        swap a i largest'
        maxHeapify a largest'
    else
        return a
