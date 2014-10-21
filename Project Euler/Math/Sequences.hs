module Math.Sequences (
    fib,
    fibs,
    triangle,
    triangles,
    pentagonal,
    pentagonals,
    hexagonal,
    hexagonals,
    collatz,
) where

-- | Fibonacci

fib n = fibs !! n

fibs = [1, 1] ++ fibs' 1 1 where
    fibs' n m = n + m : fibs' m (n + m)

-- | Geometric

-- * Triangle numbers

triangle n = n * (n + 1) `div` 2

triangles = triangles' 0 1 where
    triangles' n m = n + m : triangles' (n + m) (m + 1)

-- * Pentagonal numbers

pentagonal n = n * (3 * n - 1) `div` 2

pentagonals = map pentagonal [0..]

-- * Hexagonal numbers

hexagonal n = n * (2 * n - 1)

hexagonals = map hexagonal [0..]

-- | Collatz sequence

collatz 1 = [1]
collatz n | even n    = n : collatz (n `div` 2)
          | otherwise = n : collatz (3 * n + 1)
          
-- TODO: collatzLength (using an IntMap or InfiniteArray)
