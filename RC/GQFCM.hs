{-# LANGUAGE TupleSections, DeriveFunctor #-}

module Main where

import Control.Comonad
import Data.Function

loeb :: Functor f => f (f a -> a) -> f a
loeb ffs = fix (\fa -> fmap ($ fa) ffs)

test1 = loeb [length, (!!0), \x -> x !! 0 + x !! 1]
test2 = loeb [length, sum]

flex :: Functor f => f a -> b -> f (a,b)
flex fa b = fmap (,b) fa

loeb' :: Functor f => f (f a -> a) -> f a
loeb' ffs = fix (fmap (uncurry ($)) . flex ffs)

fill :: Functor f => f a -> b -> f b
fill fa = fmap snd . flex fa

possibility :: Comonad w => w (w a -> a) -> w a
possibility = extend wfix

data Stream a = Cons a (Stream a)
    deriving Functor
    
streamIterate :: (a -> a) -> a -> Stream a
streamIterate next seed
    = Cons seed (streamIterate next (next seed))
    
streamTake :: Int -> Stream a -> [a]
streamTake 0 _           = []
streamTake n (Cons a as) = a : streamTake (n-1) as

streamRepeat :: a -> Stream a
streamRepeat a = Cons a (streamRepeat a)

data Tape a = Tape { viewL :: Stream a, focus :: a, viewR :: Stream a }
    deriving Functor

moveL, moveR :: Tape a -> Tape a
moveL (Tape (Cons l ls) c rs) = Tape ls l (Cons c rs)
moveR (Tape ls c (Cons r rs)) = Tape (Cons c ls) r rs

tapeIterate :: (a -> a) -> (a -> a) -> a -> Tape a
tapeIterate prev next seed
    = Tape (streamIterate prev (prev seed))
           seed
           (streamIterate next (next seed))

instance Comonad Tape where
    extract   = focus
    duplicate = tapeIterate moveL moveR

main = print . streamTake 10000 . viewR . possibility $
        Tape (streamRepeat (const 0)) (const 0) (streamRepeat (succ . extract . moveL))

lfix :: ComonadApply w => w (w a -> a) -> w a
lfix f = fix undefined


