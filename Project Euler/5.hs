module Main where

import Math.NumberTheory

main = print answer

answer = head (filter (\n -> all (`divides` n) [19,18..2]) [20,40..])
