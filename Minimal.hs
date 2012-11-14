f x = case x of
        [] -> []
        (y:ys) -> case ys of
                    [] -> [y]
                    (z:zs) -> case f (z:zs) {- ys -} of
                                (a:as) -> (999:a:as)

{- non-termination...                                
g x = case x of
        [] -> []
        (y:ys) -> case g (y:ys) {- ys -} of
                    (s:ss) -> (999:ss)
-}
