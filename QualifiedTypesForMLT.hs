{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Main where

import Control.Monad.ST

choose :: forall a. a -> a -> a
choose = undefined

id' :: forall b. b -> b
id' = undefined

test :: (forall c. c -> c) -> (forall c. c -> c)
test = let
        choose :: forall a. a -> a -> a
        choose = undefined

        id' :: forall b. b -> b
        id' = undefined
    in
        choose id
