{-# LANGUAGE GADTs, KindSignatures #-}

module Main where

data T :: * -> * where
    A  ::          T a
    B  ::  Int  -> T Bool
    C  :: [Int] -> T Bool

--f :: T a -> Bool
f = \x -> case x of
            A    -> True
            B  n -> n > 0
            C  n -> null n

f' :: T a -> a
f' = \x -> case x of
            B n -> n > 0 

--f_ :: T a -> Bool            
f_ :: T Bool -> Bool
f_ = \x -> case x of
            A    -> True


--test :: T t -> t -> t
test (A   ) r = r
test (B  n) _ = n > 0
test (C  n) _ = null n


