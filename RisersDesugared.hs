module RisersDesugared where

import Data.Function (fix)

-- | Original

risers :: [Int] -> [[Int]]
risers [ ] = [ ]
risers [x] = [[x]]
risers (x : y : etc) = if x <= y then (x : s) : ss else [x] : (s : ss)
    where (s : ss) = risers (y : etc)

-- | With recursive let-bindings, without a fixpoint combinator

risers1 :: [Int] -> [[Int]]
risers1 =
  let r1 :: ([[Int]], [Int]) -> Bool -> Int -> [[Int]]
      r1 a b c = if b then (c : snd a) : (fst a) else (c : []) : (snd a : fst a)

      r2 :: [[Int]] -> ([[Int]], [Int])
      r2 d = case d of
               (e:es) -> (es, e)

      rr :: ( [Int] -> [[Int]] , Int -> [Int] -> ([[Int]], [Int]) )
      rr = ( \u -> case u of
                     []     -> []
                     (v:vs) -> case vs of
                                 []     -> (v : []) : []
                                 (w:ws) -> r1 ((snd rr) w ws) (v <= w) v
           , \x y -> r2 ((fst rr) (x : y))                                )

  in (fst rr)
  
-- | With a fixpoint combinator, without recursive let-bindings

risers2 :: [Int] -> [[Int]]
risers2 =
  let r1 :: ([[Int]], [Int]) -> Bool -> Int -> [[Int]]
      r1 a b c = if b then (c : snd a) : (fst a) else (c : []) : (snd a : fst a)

      r2 :: [[Int]] -> ([[Int]], [Int])
      r2 d = case d of
                (e:es) -> (es, e)


      rl = fix (\rf dummy -> 
                ( \u -> case u of 
                          []     -> []
                          (v:vs) -> case vs of
                                      []     -> (v : []) : []
                                      (w:ws) -> r1 ((snd (rf 42)) w ws) (v <= w) v
                , \x y -> r2 ((fst (rf 666)) (x : y))                              )
               )

  in (fst (rl 13))
