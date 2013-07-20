{-# LANGUAGE RankNTypes #-}

module Main where

s :: (exists a. (a, (a -> String))) -> String
s (x, showX) = showX x


