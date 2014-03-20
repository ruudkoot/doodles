{-# LANGUAGE ViewPatterns #-}

module Main where

t x = case x of
        [x] | x == 1 -> y
            | x == 2 -> y
          where y = x
        [a,b] | a == 1 -> z
              | b == 1 -> z
          where z = 3
          
s x = case x of
        (vp -> x) -> 3
            where vp _ = x
