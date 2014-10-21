module Main where

import Data.List.Extras

main = print answer

answer = takeLast 10 . show . sum . map (\n -> n ^ n) $ [1..1000]
