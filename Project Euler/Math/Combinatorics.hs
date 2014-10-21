module Math.Combinatorics (
    fac,
    nCr
) where

-- | Factorial

fac n | n >= 0 = product [2..n]

-- | Combinations

n `nCr` k | n > 0, k >= 0, k <= n = product [n-k+1..n] `div` product [1..k]

-- | Permutations
