module Math.NumberTheory (
    module Data.Numbers.Primes,
    divides,
    divisors,
    nDivisors,
    factor
) where

import Data.Numbers.Primes

-- | Divisability

n `divides` m = m `mod` n == 0

divisors n = divisors' 1 where
    divisors' m | m > n `div` 2 = [n]
                | m `divides` n = m : divisors' (m + 1)
                | otherwise     =     divisors' (m + 1)

nDivisors n = nDivisors' 1 where
    nDivisors' m | m > n `div` 2 = 1
                 | m `divides` n = 1 + nDivisors' (m + 1)
                 | otherwise     =     nDivisors' (m + 1)

-- | Factorization

factor n = factor' n divisors where
    divisors = takeWhile (\m -> m * m <= n) [2..]
    factor' 1 _      = []
    factor' n []     = [n]
    factor' n (d:ds) | r == 0    = d : factor' q (d:ds)
                     | otherwise =     factor' n    ds
        where (q,r) = n `divMod` d
