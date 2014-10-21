module Main where

import Math.NumberTheory

main = print answer

answer = sum (filter amicable [1..9999])

amicable a = let b = d a in a /= b && d b == a

d = sum . init . divisors
