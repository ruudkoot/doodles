{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Okasaki where

-- | Chapter 2

class Stack f a where
    empty   :: f a
    isEmpty :: f a      -> Bool
    push    :: a -> f a -> f a
    top     :: f a      -> a
    pop     :: f a      -> f a

instance Stack [] a where
    empty   = []
    isEmpty = null
    push    = (:)
    top     = head
    pop     = tail

data List a = Nil | Cons a (List a)
    deriving (Eq, Show)

instance Stack List a where
    empty               = Nil
    isEmpty  Nil        = True
    isEmpty (Cons _ _)  = False
    push                = Cons
    top     (Cons a _ ) = a
    pop     (Cons _ xs) = xs

-- * 2.2  Binary search trees

data Tree a = E | T (Tree a) a (Tree a)

class Set f a where
    emptySet :: f a
    insert   :: a -> f a -> f a
    member   :: a -> f a -> Bool

instance Ord a => Set Tree a where
    emptySet = E
    
    insert x    E        = T E x E
    insert x s@(T a y b) = case compare x y of
                             LT -> T (insert x a) y b
                             GT -> T a y (insert x b)
                             EQ -> s
    
    member _  E        = False
    member x (T a y b) = case compare x y of
                           LT -> member x a
                           GT -> member x b
                           EQ -> True

class FiniteMap f k a where
    emptyMap :: f k a
    bind     :: k -> a -> f k a -> f k a
    lookup   :: k -> f k a -> a
