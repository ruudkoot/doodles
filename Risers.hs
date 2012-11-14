le :: Int -> Int -> Bool
le = (<=)

-- risers :: [Int] -> [[Int]]
risers =
    let r1 = \a -> \b -> \c -> if b then (c : snd a) : (fst a) else (c : []) : (snd a : fst a)
     in let r2 :: [[Int]] -> ([[Int]], [Int])
            r2 = \d -> case d of (e:es) -> (es, e)
         in let rr = ( \u -> case u of { [] -> []; (v:vs) -> case vs of { [] -> (v : []) : []; (w:ws) -> r1 ((snd rr) w ws) (le v w) v } }
                     , \x -> \y -> r2 ((fst rr) (x : y))
                     )
             in fst rr
             
risers' =
    let r1 = \a -> \b -> \c -> if b then (c : snd a) : (fst a) else (c : []) : (snd a : fst a)
     in let r2 = \d -> case d of (e:es) -> (es, e)
         in let rr = ( \u -> case u of { [] -> []; (v:vs) -> case vs of { [] -> (v : []) : []; (w:ws) -> r1 ((snd rr) w ws) (le v w) v } }
                     , \x -> \y -> r2 ((fst rr) (x : y))
                     )
             in r2
             
r1 = \a -> \b -> \c -> if b then (c : snd a) : (fst a) else (c : []) : (snd a : fst a)
r2 = \d -> case d of (e:es) -> (es, e)
rr = ( \u -> case u of { [] -> []; (v:vs) -> case vs of { [] -> (v : []) : []; (w:ws) -> r1 ((snd rr) w ws) (le v w) v } }
     , \x -> \y -> r2 ((fst rr) (x : y))
     )
     

