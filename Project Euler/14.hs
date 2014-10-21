module Main where

import Math.Sequences

main = print answer

answer = snd (maximum (zip (map (length . collatz) [1..999999]) [1..999999]))
