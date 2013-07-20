module Main where

test :: a -> Int -> Int
test a x = case a of
             y -> y `seq` x
