module Main where

f :: a -> Int
f x = case x of
        _ -> 4
        
g :: a -> Int
g x = seq x 42
