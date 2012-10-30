{-# LANGUAGE NoMonomorphismRestriction #-}

module Burstall where

import Prelude hiding (length, sum)

type Monoid b = (b -> b -> b, b)

the_map :: Monoid b -> (a -> b) -> ([a] -> b)
the_map ((*), e) = \f -> foldr (*) e . map f

sum_monoid :: Monoid Int
sum_monoid = ((+), 0)

f_length = const 1
length = the_map sum_monoid f_length
length' = foldr ((+) . const 1) 0

f_sum = id
sum = the_map sum_monoid f_sum

or_monoid :: Monoid Bool
or_monoid = ((||), False)

f_member = (==)
member = the_map or_monoid . f_member

list_monoid :: Monoid [a]
list_monoid = ((++), [])

f_listmap f = \x -> [f x]
maplist f = the_map list_monoid (f_listmap f)
