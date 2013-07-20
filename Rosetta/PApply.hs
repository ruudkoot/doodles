module Main where

papply :: ((a,b) -> c, a) -> (b -> c)
papply  = \(f, a) -> \b -> f (a, b)


f :: (Int, Int) -> Bool
f (a, b) = a == b
