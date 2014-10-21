module Main where

main = do triangle <- readFile "triangle.txt"
          print (answer (map (map read . words) (lines triangle)))

answer triangle = maximum (paths [0,0] ([] : triangle))

paths xs []       = xs
paths xs (ys:yss) = paths ([0] ++ zipWith (+) (adjacent max xs) ys ++ [0]) yss

adjacent f [x1,x2]    = [x1 `f` x2]
adjacent f (x1:x2:xs) = x1 `f` x2 : adjacent f (x2:xs)
