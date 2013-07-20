module Main where

import Prelude hiding (length)

data Nested a = a :<: (Nested [a]) | Epsilon
infixr 5 :<:

nested = 1 :<: [2,3,4] :<: [[4,5],[7],[8,9]] :<: Epsilon

length :: Nested a -> Int
length Epsilon    = 0
length (_ :<: xs) = 1 + length xs
