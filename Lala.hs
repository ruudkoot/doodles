module Main where

test = let a = undefined
        in let c = \d -> d a
            in (a, c)
