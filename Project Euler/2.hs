module Main where

import Math.NumberTheory

main = print answer

answer = sum (filter even (takeWhile (<4000000) fibs))
