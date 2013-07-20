{-# LANGUAGE GADTs, KindSignatures, TypeFamilies #-}

module Main where

data T :: * -> * where
    T1 :: Int -> T Bool
    T2 :: T a
    
test :: T a -> b -> b
test (T1 n) _ = n > 0
test T2     r = r
