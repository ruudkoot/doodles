module Main where

import Math.NumberTheory

main = print answer

answer = sum (takeWhile (<2000000) primes)
