{-# LANGUAGE Rank2Types #-}

module Main where

f :: Int -> (a,b) -> (forall t. t -> [t]) -> (c, d)
f 0 (a, b) g = (g a, g b)
f n (a, b) g = f (n-1) (g a, g b) g
