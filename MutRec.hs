module Main where

test1 = let f = 1 : g
            g = 2 : h
            h = 3 : f
         in f
         
test2 = let (f, g, h) = (1 : g, 2 : h, 3 : f)
         in f
         
fst3 (x, _, _) = x
snd3 (_, y, _) = y
trd3 (_, _, z) = z
         
test3 = let r = (1 : snd3 r, 2 : trd3 r, 3 : fst3 r)
         in fst3 r

test4 = let f       = 1 : (g f)
            g f'    = 2 : (h f' g)
            h f' g' = 3 : f'
         in f
         
test5 = let f g' h' = 1 : (g' h')
         in let g h'    = 2 : h'
             in let h       = 3 : f g h
                 in f g h

test6 = let f = fst3 r
            g = snd3 r
            h = trd3 r
            r = (1 : g, 2 : h, 3 : f)
         in f

