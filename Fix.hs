module Main where

fix f = f (fix f)

fix' f = let x = f x in x

test n = \r -> if n == 5 then 10 else 2 * (r (n + 1))

