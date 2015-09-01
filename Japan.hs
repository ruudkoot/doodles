{- Japanese Puzzle Solver ------------------------------------------}
{-                                                                 -}
{-  Copyright (c) 2005, Rudy Koot                                  -}
{-  Licenced under GNU General Public License version 2 or later.  -}
{-                                                                 -}
{-------------------------------------------------------------------}

module Main where

data Color = Black
           | White Int
    deriving (Eq, Show)

type Fingerprint = [[(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)]]

horizontal = [ [24,7,11],[6,12,12,7],[24,14],[13,12,10],[9,22,11],[20,17],[14,14,14],[3,8,12,6],[21,10,12],[20,17] ] :: [[Int]]
vertical   = [ [10,10,10],[9,9,9,9],[23,22],[19,11,7,5],[31,11],[10,17,11],[10,25,3],[14,7,4],[8,29,5],[12,4,28] ] :: [[Int]]

invertColor :: Color -> Color
invertColor Black     = White 0
invertColor (White _) = Black

{- Functions that build [[[Color]]] -}

grow :: [Int] -> (Int, [Int], [Int])
grow l = (y, z, l)
    where y = g z (length l)
          z = (map f l)

f :: Int -> Int
f x | x <=  9   = 1
    | x <= 18   = 2
    | x <= 27   = 3
    | x <= 36   = 4

g :: [Int] -> Int -> Int
g z n = 10 - (n - 1) - (sum z)

reap :: (Int, [Int], [Int]) -> [[[Color]]]
reap (n, a, z) = map (\x->toColor Black x) (grim n 0 (fool (zip a z) ) )

fool :: [(Int,Int)] -> [(Int,Int)]
fool a = [(0,0)] ++ (horse a) ++ [(0,0)]

horse :: [(Int,Int)] -> [(Int,Int)]
horse (a:[]) = [a]
horse (a:as) = a : (1,0) : horse as

toColor :: Color -> [(Int,Int)] -> [[Color]]
toColor _         []         = [[]]
toColor Black     ((a,_):as) = map (\x->(take a (repeat Black))++x) (toColor (White 0) as)
toColor (White _) ((a,b):as) = [ x++y | x<-(map paint (distribute 0 a b)), y<-(toColor Black as) ]

paint:: [Int] -> [Color]
paint []     = []
paint (n:ns) = White n : paint ns

grim :: Int -> Int -> [(Int,Int)] -> [[(Int,Int)]]
grim n x l@((a,b):[]) = [[(n+a,b)]]
grim n x l@((a,b):as) | x <= n    = ( map (( (x+a,b) ):) (grim (n-x) 0 as) ) ++ grim n (x+1) l
                      | otherwise = []

distribute :: Int -> Int -> Int -> [[Int]]
distribute n 1 s = [[s]]
distribute n l s | n < 1         = distribute (max 1 (s-9*(l-1))) l s
--               | n+9*(l-1) < s = distribute (max 1 (s-9*(l-1))) l s
                 | n+(l-1) > s   = []
                 | n > 9         = []
                 | otherwise     = map (n:) (distribute 0 (l-1) (s-n)) ++ distribute (n+1) l s

{- Several gigabytes of data -}

h = map (\x->concat (reap x)) (map grow horizontal)
v = map (\x->concat (reap x)) (map grow vertical)

t :: Fingerprint
t = replicate 10 ( replicate 10 (True, True, True, True, True, True, True, True, True, True) )

{- Functions that solve a pair of [[[Color]]]s -}

main = print $ map (\(n,x)->showFingerprint x) ( iterate (solve.solve) (1, t) )

showFingerprint :: Fingerprint -> String
showFingerprint f = ">>> " ++ showFingerprint' (concat f)

showFingerprint' :: [(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)] -> String
showFingerprint' [] = ""
showFingerprint' (a:as) = showFingerprint'' a ++ showFingerprint' as

showFingerprint'' :: (Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool) -> String
showFingerprint'' (True, False, False, False, False, False, False, False, False, False) = "X"
showFingerprint'' (False, True, False, False, False, False, False, False, False, False) = "1"
showFingerprint'' (False, False, True, False, False, False, False, False, False, False) = "2"
showFingerprint'' (False, False, False, True, False, False, False, False, False, False) = "3"
showFingerprint'' (False, False, False, False, True, False, False, False, False, False) = "4"
showFingerprint'' (False, False, False, False, False, True, False, False, False, False) = "5"
showFingerprint'' (False, False, False, False, False, False, True, False, False, False) = "6"
showFingerprint'' (False, False, False, False, False, False, False, True, False, False) = "7"
showFingerprint'' (False, False, False, False, False, False, False, False, True, False) = "8"
showFingerprint'' (False, False, False, False, False, False, False, False, False, True) = "9"
showFingerprint'' _ = "?"

solve :: (Int, Fingerprint) -> (Int, Fingerprint)
solve (1, f) = (2, z f h)
solve (2, f) = (1, z f v)

z :: Fingerprint -> [[[Color]]] -> Fingerprint
z f c = transpose (takeFingerprint (filterConflicts f c))

takeFingerprint :: [[[Color]]] -> Fingerprint
takeFingerprint [] = []
takeFingerprint a = map (\x->takeFingerprint' 0 x) a

takeFingerprint' :: Int -> [[Color]] -> [(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)]
takeFingerprint' n c | n > 9    = []
                     | otherwise = takeFingerprint'' n c : takeFingerprint' (n+1) c

takeFingerprint'' :: Int -> [[Color]] -> (Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)
takeFingerprint'' n []     = (False, False, False, False, False, False, False, False, False, False)
takeFingerprint'' n (c:cs) = orFingerprint n c (takeFingerprint'' n cs)

orFingerprint :: Int -> [Color] -> (Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool) -> (Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)
orFingerprint n c (b0, b1, b2, b3, b4, b5, b6, b7, b8, b9) = ( b0 || c!!n == Black
                                                             , b1 || c!!n == White 1
                                                             , b2 || c!!n == White 2
                                                             , b3 || c!!n == White 3
                                                             , b4 || c!!n == White 4
                                                             , b5 || c!!n == White 5
                                                             , b6 || c!!n == White 6
                                                             , b7 || c!!n == White 7
                                                             , b8 || c!!n == White 8
                                                             , b9 || c!!n == White 9 )

filterConflicts :: Fingerprint -> [[[Color]]] -> [[[Color]]]
filterConflicts f c = c

transpose :: [[a]] -> [[a]]
transpose [rij] = map singleton rij
  where singleton x = [x]
transpose (xs:xss) = zipWith (:) xs (transpose xss)

{-

findConflicts :: Int -> [[[Color]]] -> [[[Color]]] -> [[[Color]]]
findConflicts n []     b = b
findConflicts n (a:as) b = findConflicts (n+1) as (findConflictsOnRow n 0 a b)

findConflictsOnRow :: Int -> Int -> [[Color]] -> [[[Color]]] -> [[[Color]]]
--findConflcitsOnRow n m [] b       = b
findConflictsOnRow n 10 a b       = b
findConflictsOnRow n m l@(a:as) b | isAll m (a!!m) as = findConflictsOnRow n (m+1) l (removeConflicts b (a!!m) m n)
                                  | otherwise         = findConflictsOnRow n (m+1) l b

isAll :: Int -> Color -> [[Color]] -> Bool
isAll m c []     = True
isAll m c (a:as) | (a!!m) == c = isAll m c as
                 | otherwise   = False

removeConflicts :: [[[Color]]] -> Color -> Int -> Int -> [[[Color]]]
removeConflicts b c m n = ( take m b ) ++ ( [removeConflictsOnColumn (b!!m) c n] ) ++ ( drop (m+1) b )

removeConflictsOnColumn :: [[Color]] -> Color -> Int -> [[Color]]
removeConflictsOnColumn [] _ _     = []
removeConflictsOnColumn (b:bs) c n | b!!n == c = b : removeConflictsOnColumn bs c n
                                   | otherwise = removeConflictsOnColumn bs c n

-}


