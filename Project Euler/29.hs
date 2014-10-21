module Main where

import           Data.List
import qualified Data.List.Sorted as Sorted

main = print answer

answer = length (Sorted.nub (sort [ a^b | a <- [2..100], b <- [2..100] ]))
