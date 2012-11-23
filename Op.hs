{-# LANGUAGE TypeOperators #-}

(#) :: Int -> Int -> Int -> Int
(#) a b c = a + b + c

data (:#)
    = (:#) Int Int Int
    deriving (Eq, Ord, Show)
    
x = (2 :# 3) 4

y = case x of
        (:#) a b c -> a + b + c
