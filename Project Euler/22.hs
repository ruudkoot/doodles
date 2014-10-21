module Main where

import Data.Char (ord)
import Data.List (sort)

main = do names <- readFile "names.txt"
          print (answer (read ("[" ++ names ++ "]")))

answer = sum . zipWith (*) [1..] . map (sum . map (\c -> ord c - ord 'A' + 1)) . sort
