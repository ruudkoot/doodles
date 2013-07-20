module Main where

papply = curry

curry3 :: ((a, b, c) -> r) -> a -> b -> c -> r
curry3 f x y z = f (x, y, z)

papply2 :: ((a, b) -> r) -> a -> b -> r
papply2 f x = \y -> f (x, y)

papply3 :: ((a, b, c) -> r) -> a -> (b, c) -> r
papply3 f x = \(y, z) -> f (x, y, z)

f :: (Integer, Integer, Integer) -> Integer
f (a, b, x) = a * x  + b

f' :: (Integer, (Integer, Integer)) -> Integer
f' (a, (b, x)) = a * x  + b

g :: Integer -> Integer -> Integer -> Integer
g a b x = a * x + b

g' :: Integer -> (Integer -> (Integer -> Integer))
g' = \a -> \b -> \x -> a * x + b

main = let u  = curry3 f 7 9
           v  = papply2 (papply3 f 7) 9
           u' = \x -> curry (curry f' x)
           v' = papply (papply f' 7) 9
           w  = g 7 9
       in print [map u [1..5], map v [1..5], map w [1..5]]

