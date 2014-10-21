module Main where

import Data.List.Sorted
import Math.Sequences

main = print answer

answer = inAll [triangles, pentagonals, hexagonals] !! 2
