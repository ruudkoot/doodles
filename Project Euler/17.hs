module Main where

main = print answer

answer = length (filter (\c -> c /= ' ' && c /= '-') (concatMap spellNumber [1..1000]))

spellNumber  :: Integer -> String
spellNumber n | n >= 1000000 = undefined
              | n >=    1000 = let (a,b) = n `divMod` 1000 in spellNumber   a       ++ " " ++ spellNumber' 1000 ++ if b == 0 then "" else " "     ++ spellNumber  b
              | n >=     100 = let (a,b) = n `divMod`  100 in spellNumber   a       ++ " " ++ spellNumber'  100 ++ if b == 0 then "" else " and " ++ spellNumber  b
              | n >=      20 = let (a,b) = n `divMod`   10 in spellNumber' (a * 10)                             ++ if b == 0 then "" else "-"     ++ spellNumber' b
              | n >=       0 = spellNumber' n
    where
        spellNumber'    0 = "zero"
        spellNumber'    1 = "one"
        spellNumber'    2 = "two"
        spellNumber'    3 = "three" 
        spellNumber'    4 = "four"
        spellNumber'    5 = "five"
        spellNumber'    6 = "six"
        spellNumber'    7 = "seven"
        spellNumber'    8 = "eight"
        spellNumber'    9 = "nine"
        spellNumber'   10 = "ten"
        spellNumber'   11 = "eleven"
        spellNumber'   12 = "twelve"
        spellNumber'   13 = "thirteen"
        spellNumber'   14 = "fourteen"
        spellNumber'   15 = "fifteen"
        spellNumber'   16 = "sixteen"
        spellNumber'   17 = "seventeen"
        spellNumber'   18 = "eighteen"
        spellNumber'   19 = "nineteen"
        spellNumber'   20 = "twenty"
        spellNumber'   30 = "thirty"
        spellNumber'   40 = "forty"
        spellNumber'   50 = "fifty"
        spellNumber'   60 = "sixty"
        spellNumber'   70 = "seventy"
        spellNumber'   80 = "eighty"
        spellNumber'   90 = "ninety"
        spellNumber'  100 = "hundred"
        spellNumber' 1000 = "thousand"
