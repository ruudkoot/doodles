module Main where

import Math.NumberTheory

main = print answer

answer = sum (filter abundant [1..28123])

abundant n = sum (init (divisors n)) > n
