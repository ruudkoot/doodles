module Main where

isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd (n - 1)

isOdd :: Int -> Bool
isOdd 1 = True
isOdd n = isEven (n - 1)

isEven = fst f
    where
        f :: (Int -> Bool, Int -> Bool)
        f (isEven
