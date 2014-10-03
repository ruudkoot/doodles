{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Chapter5 where

import           Prelude hiding (head, tail, last, init)
import qualified Prelude as P

import Data.Monoid

-- | 5.1  Queues

-- * Exercise 5.1

class Monoid (f a) => Deque f a where
    null :: f a      -> Bool
    cons :: a -> f a -> f a
    head :: f a      -> Maybe a
    tail :: f a      -> Maybe (f a)
    snoc :: f a -> a -> f a
    last :: f a      -> Maybe a
    init :: f a      -> Maybe (f a)

data Dequeue a = Dequeue [a] [a]

maintain :: [a] -> [a] -> Dequeue a
maintain [] ys = let (xs', ys') = halve ys in Dequeue xs' ys'
maintain xs ys = Dequeue xs ys

halve :: [a] -> ([a], [a])
halve xs = splitAt (length xs `div` 2) xs

instance Monoid (Dequeue a) where
    mempty
        = Dequeue [] []
    mappend (Dequeue xs1 ys1) (Dequeue xs2 ys2)
        = Dequeue xs1 (ys2 ++ reverse xs2 ++ ys1)

instance Deque Dequeue a where
    null (Dequeue [] _) = True
    null _              = False
    
    cons x (Dequeue xs ys) = Dequeue (x : xs) ys
    
    head (Dequeue []      _) = Nothing
    head (Dequeue (x : _) _) = Just x
    
    tail (Dequeue []       _ ) = Nothing
    tail (Dequeue (_ : xs) ys) = Just (maintain xs ys)
    
    snoc (Dequeue xs ys) y = Dequeue xs (y : ys)

    last (Dequeue [] _      ) = Nothing
    last (Dequeue _  []     ) = Nothing
    last (Dequeue _  (y : _)) = Just y
    
    init (Dequeue [] _ ) = Nothing
    init (Dequeue xs ys) = Just (maintain (P.init xs) ys)
    
instance Show a => Show (Dequeue a) where
    show (Dequeue xs ys) = P.init (show xs) ++ ";" ++ P.tail (show (reverse ys))
