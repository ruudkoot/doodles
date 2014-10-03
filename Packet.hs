{-# LANGUAGE RankNTypes #-}

module Main where

main = putStrLn . show $ test

data F = F (forall x. Show x => x -> String)

test = F (error "XXX") `seq` ()
