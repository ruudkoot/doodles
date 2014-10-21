module Math.List where

subseg n xxs@(x:xs)
    | length xxs < n = []
    | otherwise      = take n xxs : subseg n xs

palindrome xs = xs == reverse xs
