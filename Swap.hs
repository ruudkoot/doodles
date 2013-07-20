{-# LANGUAGE GADTs #-}

module Main where

test = let swap (a,b) = (b,a)
        in (swap (True, False), swap (1,2))
