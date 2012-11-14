{-# LANGUAGE ScopedTypeVariables #-}

module Main where

instance Show (a -> b) where
    show f = "[lambda]"

crash = error "CRASH"

test = \x -> if x then crash else crash

main = do print $ case test of (x :: Bool -> Bool) -> x False
