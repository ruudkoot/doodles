module Main where

import Math.Numerology

main = print answer

answer = product (map (champernowne !!) [1,10,100,1000,10000,100000,1000000])
