module Main where

import Data.Array

test = array ((1,1),(5,10)) [((i,j),2*i+j) | i <- [1..5], j <- [1..10]]
