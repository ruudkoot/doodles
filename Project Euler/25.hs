module Main where

import Data.List
import Data.Maybe
import Math.NumberTheory

main = print answer

answer = fst (fromJust (find ((==1000) . length . show . snd) (zip [1..] fibs)))
