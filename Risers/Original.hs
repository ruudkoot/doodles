module Risers.Original where

risers :: [Int] -> [[Int]]
risers [ ] = [ ]
risers [x] = [[x]]
risers (x : y : etc) = if x <= y then (x : s) : ss else [x] : (s : ss)
    where (s : ss) = risers (y : etc)
