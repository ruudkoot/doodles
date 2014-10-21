{- DP/memoization over n -}
{- this approach gives too many permutations -}

module Main where

import Math.Numerology

main = print answer

answer = xs where

    coins = [1, 2, 5, 10, 20, 50, 100, 200]

    xs = map f [0..200]
    
    f 0 = 1
    f n = sum (map (\c -> if n - c < 0 then 0 else xs !! (n - c)) coins)
