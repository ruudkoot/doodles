{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Test.QuickCheck

f [a]   = h a
    where h [] = 0
          h (ss:s) = 1 + h s
f (b:a) = if g b > f a then g b else f a
    where g f = foldr (\f g -> g + 1) 0 f

lengthOfLongest :: [[Int]] -> Int
lengthOfLongest = maximum . map length

main = quickCheck (\xs -> not (null xs) ==> f xs == lengthOfLongest xs)
{-
f []     = []
f (x:xs) | x < 0     = x + x     : filter odd (f xs)
        | even x    = compute x : f             xs
        | otherwise = 3 * x - 1 : f             xs
        
compute = id
-}
