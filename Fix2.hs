-- Polyvariadic fixed-point combinators

module Main where

fix :: (t -> t) -> t
fix  f = f (      fix  f  )

fix' :: ((a -> t) -> a -> t) -> a -> t
fix' f = f (\x -> fix' f x)

delay :: (a -> b) -> a -> b
delay h = \x -> h x

fix'' :: ((a -> t) -> a -> t) -> a -> t
fix'' f = f (delay (fix'' f))

anonFib :: (Integer -> Integer) -> Integer -> Integer
anonFib = \f i -> case i of {1 -> 1; _ -> i * f (i-1)}

p, p', p'' :: Integer
p   = fix   anonFib 5
p'  = fix'  anonFib 5
p'' = fix'' anonFib 5

type I = Integer
type D = Double

i2d = fromInteger
d2i = round

anonFib2 :: (I -> I, D -> D) -> (I -> I, D -> D)
anonFib2 = \(f,g) ->
    ( \x -> case x of {1 -> 1; _ -> x * d2i (g (i2d x-1))}
    , \y -> case y of {1 -> 1; _ -> y * i2d (f (d2i y-1))} )

q  = fst (fix anonFib2) 5
--q' = fst (fix2' (anonFib1,anonFib2)) 5


