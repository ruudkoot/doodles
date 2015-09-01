module Main where

place :: Int -> [Int] -> [[Int]]
place w xs =
    let n  = length xs
        mw = sum xs + n - 1
     in map (makeStuff xs) (extraPad (n-1) (w-mw))
