{-# LANGUAGE NoMonomorphismRestriction #-}

module Burstall where

import Prelude hiding (length, sum)
import Data.Set hiding (map, foldr)

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

-- 3.3  Categories computationally

data Cat o a = Cat (a -> o) (a -> o) (o -> a) (a -> a -> a)

-- 3.4  Categories as values

-- 3.4.1  The category of finite sets

data Set_Arrow a = Set_Arrow (Set a) (a -> a) (Set a)

set_s (Set_Arrow a _ _) = a
set_t (Set_Arrow _ _ b) = b
set_ident a = Set_Arrow a id a
set_comp (Set_Arrow c g d) (Set_Arrow a f b)
    | b == c = Set_Arrow a (g . f) d

finSet = Cat set_s set_t set_ident set_comp


