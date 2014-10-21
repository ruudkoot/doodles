module Data.List.Sorted (
    inAll,
    nub
) where

-- Find elements contained in all infinite lists.
inAll :: Ord a => [[a]] -> [a]
inAll xss = let x = minimum (map head xss)
             in if all ((==x) . head) xss then
                    x : inAll (map tail xss)
                else
                    inAll (map (\(y:ys) -> if y == x then ys else y : ys) xss)

-- Remove duplicated from a sorted lists
nub []         = []
nub [x]        = [x]
nub (x1:x2:xs) | x1 == x2  =      nub (x2:xs)
               | otherwise = x1 : nub (x2:xs)
