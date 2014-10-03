{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Chapter3 where

-- | 3.1  Leftist heaps

class Ord a => Heap f a where
    empty     :: f a
    isEmpty   :: f a -> Bool
    insert    :: a -> f a -> f a
    merge     :: f a -> f a -> f a
    findMin   :: f a -> a
    deleteMin :: f a -> f a

data LeftistHeap a = E | T Int a (LeftistHeap a) (LeftistHeap a)
    deriving (Eq, Show)

instance Ord a => Heap LeftistHeap a where
    empty = E

    isEmpty E = True
    isEmpty _ = False

    insert x h = merge (T 1 x E E) h

    merge h E = h
    merge E h = h
    merge h1@(T _ x a1 b1) h2@(T _ y a2 b2)
        | x <= y    = makeT x a1 (merge b1 h2)
        | otherwise = makeT y a2 (merge h1 b2)
      where makeT x a b | rank a >= rank b = T (rank b + 1) x a b
                        | otherwise        = T (rank a + 1) x b a
              where rank  E          = 0
                    rank (T r _ _ _) = r

    findMin (T _ x a b) = x
    
    deleteMin (T _ x a b) = merge a b

-- | 3.2  Binomial heaps

newtype BinomialHeap a = [Tree a]

instance Ord a => Heap BinomialHeap a where
    
