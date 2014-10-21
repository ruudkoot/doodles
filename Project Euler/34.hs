module Main where

import Math.Combinatorics
import Math.Numerology

main = print answer

answer = let (x1:x2:_) = filter (\n -> n == sum (map fac (digits n))) [10..]
          in x1 + x2

-- TODO: Prove that no larger numbers can exist.
--       (Sketch: Numbers grow quicker than 9! + 9! + ...)
