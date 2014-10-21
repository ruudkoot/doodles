module Main where

import Math.Numerology

main = print answer

answer = sum (filter (\n -> n == sum (map (^5) (digits n))) [10..999999])

-- TODO: Prove that no larger numbers can exist.
--       (Sketch: Numbers grow quicker than 9^5 + 9^5 + ...)
