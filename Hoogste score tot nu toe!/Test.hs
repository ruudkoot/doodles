module Main where

import Data.Char

main = do c1 <- getChar
          c2 <- getChar
          c3 <- getChar
          putStrLn $ "[" ++ show (ord c1) ++ " " ++ show (ord c2) ++ " " ++ show (ord c3) ++ "]"
          main
