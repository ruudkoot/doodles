module Main where

import Math.NumberTheory

main = print answer

answer = sum (filter (\n -> 3 `divides` n || 5 `divides` n) [1..999])
