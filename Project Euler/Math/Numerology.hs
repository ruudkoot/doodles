module Math.Numerology (
    digits,
    digitsInBase,
    sumDigits,
    sumDigitsInBase,
    champernowne
) where

-- | Digits

digits = digitsInBase 10

digitsInBase r = reverse . digitsInBase' where
    digitsInBase' 0 = []
    digitsInBase' n = let (p,q) = n `divMod` r in q : digitsInBase' p

-- | Digit summation

sumDigits = sumDigitsInBase 10

sumDigitsInBase r n = snd (until ((==0) . fst) (\(n,s) -> let (p,q) = n `divMod` r in (p,s+q)) (n,0))

-- | Champernowne's constant

champernowne = 0 : concatMap digits [1..]
