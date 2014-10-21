{-# LANGUAGE ParallelListComp #-}

module {-Data.List.Algorithms-}Main where

-- Make Data.Array, Data.Sequence versions
-- Make use of the wavefront (reorder array for better cache effects, parallize)
-- Make recursive unboxed arrays work (or use the wavefront?)
-- * Invent an new array construcotr that passes the *already* constucted part?
-- * Invernt a program analysys
-- * Somehow encode the anaylssis in the typesystem
-- Make dynamic programming composable through a combinator library
-- Long/short breask even around 200

import Data.Array

longestCommonSubcycle4 :: String -> String -> Int
longestCommonSubcycle4 as bs
    = maximum [fst (longestCommonSubsequence xs ys) | xs <- rotations as, ys <- rotations bs]

longestCommonSubcycle3 :: String -> String -> Int
longestCommonSubcycle3 as bs
    = maximum [fst (longestCommonSubsequence xs bs) | xs <- rotations as]

test zs n = (zs, n, and [longestCommonSubcycle3 a b == longestCommonSubcycle4 a b | a <- strings zs n, b <- strings zs n])

-- main = print (test "01" 10)
-- main = print (test "ABC" 7)
-- main = print (test "ABCD" 6)
-- main = print (test "ABCDE" 5)
-- main = print (test "ABCDEF" 5)
--              -----------------> <4h
{-
main = do print (test "01" 10)
          print (test "ABC" 7)
          print (test "ABCD" 6)
          print (test "ABCDE" 5)
          print (test "ABCDEF" 4)
          print (test "ABCDEF" 5)
-}

-- main = print (test "ABC" 6)
main = print (longestCommonSubsequenceL z z)

strings :: String -> Int -> [String]
strings as 0 = [[]]
strings as n = [a:bs | a <- as, bs <- strings as (n-1)]

rotations :: String -> [String]
rotations = rotations' []
    where rotations' :: String -> String -> [String]
          rotations' xs []     = []
          rotations' xs (y:ys) = (y : ys ++ xs) : rotations' (xs ++ [y]) ys

-- | Longest common subsequence

longestCommonSubsequence :: Eq a => [a] -> [a] -> (Int, [a])
longestCommonSubsequence x y =
    let m = length x
        n = length y
        -- c = array ((0, 0), (m, n)) [((i, j), f i j x y) | i <- [0..m], j <- [0..n] | x <- undefined:xs, y <- undefiend:ys]
        -- c = array ((0, 0), (m, n)) [((fst i, fst j), f i j) | i <- zip [0..m] (undefined:x), j <- zip [0..n] (undefined:y)]
        c = array ((0, 0), (m, n)) [((i, j), f i j) | i <- [0..m], j <- [0..n]]
        
            where f 0 _ = 0
                  f _ 0 = 0
                  f i j | x!!(i-1) == y!!(j-1)     = c!(i-1, j-1) + 1
                        | c!(i-1, j) >= c!(i, j-1) = c!(i-1, j  )  
                        | otherwise                = c!(i  , j-1)
        reconstruct 0 _ = id
        reconstruct _ 0 = id
        reconstruct i j | c!(i-1,j) == c!(i,j) = reconstruct (i-1)  j
                        | c!(i,j-1) == c!(i,j) = reconstruct  i    (j-1)
                        | otherwise            = reconstruct (i-1) (j-1) . (x!!(i-1):)
    in (foldl (\x r -> r `seq` x) (c!(0,0)) [(i,j)|i<-[0..m],j<-[0..n]], reconstruct m n [])

foldl' f z []     = z
foldl' f z (x:xs) = let z' = z `f` x 
                    in seq z' $ foldl' f z' xs

longestCommonSubsequenceL :: Eq a => [a] -> [a] -> (String, [a])
longestCommonSubsequenceL x y =
    let m = length x
        n = length y
        -- c = array ((0, 0), (m, n)) [((i, j), f i x' j y') | i <- [0..m], j <- [0..n] | x' <- undefined:x, y' <- undefined:y]
        c = array ((0, 0), (m, n)) [((fst i, fst j), f i j) | i <- zip [0..m] (undefined:x), j <- zip [0..n] (undefined:y)]
        -- c = array ((0, 0), (m, n)) [((i, j), f i j) | i <- [0..m], j <- [0..n]]
        
            where f (0,_) _ = 0
                  f _ (0,_) = 0
                  f (i,x) (j,y) | x == y                   = c!(i-1, j-1) + 1
                                | c!(i-1, j) >= c!(i, j-1) = c!(i-1, j  )  
                                | otherwise                = c!(i  , j-1)
        reconstruct 0 _ = id
        reconstruct _ 0 = id
        reconstruct i j | c!(i-1,j) == c!(i,j) = reconstruct (i-1)  j
                        | c!(i,j-1) == c!(i,j) = reconstruct  i    (j-1)
                        | otherwise            = reconstruct (i-1) (j-1) . (x!!(i-1):)
    in ({-foldl' (\x r -> r `seq` x) (c!(m,n)) [(i,j)|i<-[0..m],j<-[0..n]]-}concat [show (c!(i,j))|i<-[0..m],j<-[0..n]], reconstruct m n [])
    
-- * Longest common subsequence (reversed, faster and lazier)

-- * Longest common subsequence (length only, needs only linear memory)

-- * Longest common subsequence with custom comparator

-- * Longest common subsequence of three strings

longestCommonSubsequence3 :: Eq a => [a] -> [a] -> [a] -> (Int, [a])
longestCommonSubsequence3 x y z =
    let m = length x
        n = length y
        o = length z
        c = array ((0, 0, 0), (m, n, o)) [((i, j, k), f i j k) | i <- [0..m], j <- [0..n], k <- [0..o]]
            where f 0 _ _ = 0
                  f _ 0 _ = 0
                  f _ _ 0 = 0
                  f i j k | x!!(i-1) == y!!(j-1) && y!!(j-1) == z!!(k-1) = c!(i-1, j-1, k-1) + 1
                          | c!(i-1, j, k) >= c!(i, j-1, k) && c!(i-1, j, k) >= c!(i, j, k-1) = c!(i-1, j, k)
                          | c!(i, j-1, k) >= c!(i, j, k-1) = c!(i, j-1, k)
                          | otherwise                = c!(i, j, k-1)
        reconstruct 0 _ _ = id
        reconstruct _ 0 _ = id
        reconstruct _ _ 0 = id
        reconstruct i j k | c!(i-1,j,k) == c!(i,j,k) = reconstruct (i-1)  j     k
                          | c!(i,j-1,k) == c!(i,j,k) = reconstruct  i    (j-1)  k
                          | c!(i,j,k-1) == c!(i,j,k) = reconstruct  i     j    (k-1)
                          | otherwise                = reconstruct (i-1) (j-1) (k-1) . (x!!(i-1):)
    in (c!(m, n, o), reconstruct m n o [])
{-
longestCommonSubsequenceN :: Eq a => [[a]] -> (Int, [a])
longestCommonSubsequenceN xs =
    let n  = length xs
        zs = replicate n 0
        ms = map length xs    -- mapLenght or fuse
        c = array (zs, ms) [(is, f is) | is <- [zs..ms]]
            where f is | hasZero is           = 0
                       | equalAtIndices xs is = c!(i-1, j-1, k-1) + 1
                       | c!(i-1, j, k) >= c!(i, j-1, k) && c!(i-1, j, k) >= c!(i, j, k-1) = c!(i-1, j, k)
                       | c!(i, j-1, k) >= c!(i, j, k-1) = c!(i, j-1, k)
                       | otherwise                = c!(i, j, k-1)

        hasZero :: [a] -> Bool
        hasZero []     = False
        hasZero (0:_)  = True
        hasZero (_:xs) = hasZero xs
        
        equalAtIndices :: [a] -> [a] -> Bool
        equalAtIndices [_]      _        = True
        equalAtIndices (x:y:zs) (i:j:ks) = x!!(i-1) == y!!(j-1) && equalAtIndices (y:zs) (j:ks)
        
        greaterThanHigherIndices :: [a] -> [a] -> Bool
        greaterThanHigherIndices hs (i:is) = and (map (c!(hs++[i-1]++is) >=) (higherIndices [] is))
            where higherIndices _ [] = []
                  higherIndices gs (j:js) = (hs++[i]++gs++[j-1]++js) : higherIndices (gs++[j]) js
{-
        reconstruct 0 _ _ = id
        reconstruct _ 0 _ = id
        reconstruct _ _ 0 = id
        reconstruct i j k | c!(i-1,j,k) == c!(i,j,k) = reconstruct (i-1)  j     k
                          | c!(i,j-1,k) == c!(i,j,k) = reconstruct  i    (j-1)  k
                          | c!(i,j,k-1) == c!(i,j,k) = reconstruct  i     j    (k-1)
                          | otherwise                = reconstruct (i-1) (j-1) (k-1) . (x!!(i-1):)-}
    in (c!(m, n, o), undfined{-reconstruct m n o []-})
-}
-- | Is subsequence?
    
isSubsequence :: String -> String -> Bool
isSubsequence [] _          = True
isSubsequence _ []          = False
isSubsequence (x:xs) (y:ys) | x == y    = isSubsequence xs ys
                            | otherwise = isSubsequence (x:xs) ys
                            
printArray :: Array (Int,Int) Int -> String
printArray arr = let (_,(m,n)) = bounds arr
                  in concat [ concat [ show (arr!(i,j))| j <- [0..n] ] ++ "\n" | i <- [0..m] ]

z = concat (replicate 200 ['A'..'Z'])                  
s1  = "ACCGGTCGAGTGCGCGGAAGCCGGCCGAA"
s2  = "GTCGTTCGGAATGCCGTTGCTCTGTAAA"
s3  = snd (longestCommonSubsequence s1 s2)
s3' = snd (longestCommonSubsequence s2 s1)
t1  = s3  `isSubsequence` s1
t1' = s3' `isSubsequence` s1
t2  = s3  `isSubsequence` s2
t2' = s3' `isSubsequence` s2
