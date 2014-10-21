module Main where

import Data.List
import Math.List

main = print answer

answer = head . filter (palindrome . show) . reverse . sort $
            [ i * j | i <- [100..999], j <- [100..999] ]
