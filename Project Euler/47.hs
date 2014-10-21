module Main where

import Control.Arrow
import Data.List.Extras
import Math.NumberTheory

main = print answer

answer = f (zip [1..] (map (length . nubSorted . factor) [1..])) where
    f ((n,4):(_,4):(_,4):(_,4):_) = n
    f (_:xs)                      = f xs

