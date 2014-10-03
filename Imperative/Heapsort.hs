{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

module Main where

import Monad.Imperative

class (Integral i, Ix i, Ord i) => HeapIx i where
    parent :: i -> i
    left   :: i -> i
    right  :: i -> i
    
instance (Integral i, Ix i) => HeapIx i where
    parent i = i `div` 2
    left   i = 2 * i
    right  i = 2 * i + 1

type Heap m i e = (i, Array m i e)

heapSize :: Heap m i e -> i
heapSize (n, _) = n

(!) :: (MonadImperative m, HeapIx i) => Heap m i e -> i -> m e
(!) (n, a) i
    | n < i     = error "Heapsort.get: index out of bounds"
    | otherwise = readA a i
    
swapH (n, a) i (m, b) j
    | i <= n, j <= m = swapA a i b j
    | otherwise      = error "Heapsort.swapH: indices out of bounds"
    
maxHeapify :: (MonadImperative m, HeapIx i, Ord e) => Heap m i e -> i -> m ()
maxHeapify a i = do
    let l = left  i
    let r = right i
    largest <- newR undefined
    a_l <- a ! l
    a_i <- a ! i
    if l <= heapSize a && a_l > a_i then
        writeR largest l
    else
        writeR largest i
    a_r <- a ! r
    largest' <- readR largest
    a_largest <- a ! largest'
    if r <= heapSize a && a_r > a_largest then
        writeR largest r
    else
        skip
    largest' <- readR largest
    if largest' /= i then do
        swapH a i a largest'
        maxHeapify a largest'
    else
        skip
    return ()
