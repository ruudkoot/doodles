{-# LANGUAGE GADTs, KindSignatures #-}
{-# LANGUAGE StandaloneDeriving    #-}

module Main where

import qualified Data.List as L

data Set :: * -> * where
    Set :: Ord a => [a] -> Set a

union :: Set a -> Set a -> Set a
union (Set s) (Set t) = Set (Data.List.union s t)

