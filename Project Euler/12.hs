{- factor + combinatorics -}

module Main where

import Control.Arrow
import Data.List
import Data.Maybe
import Math.NumberTheory

main = print answer

answer = fst . fromJust . find ((>200) . snd) . map (id &&& nDivisors) $
            triangleNumbers
