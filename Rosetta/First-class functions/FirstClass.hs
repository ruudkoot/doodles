module Main where

f :: [[Integer] -> [Integer]]
f = let a = 1
        b = 3
     in [map (\x -> a * x + b), map (\x -> b * x + a)]

main = print (map ($ [1, 2, 3, 4, 5]) f)

