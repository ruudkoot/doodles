{-# LANGUAGE Rank2Types #-}

module Main where

f :: (forall s. s -> t) -> (t, t)
f x = (x True, x False)
