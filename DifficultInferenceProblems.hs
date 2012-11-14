-- test1 :: [Bool -> Integer] -> Integer
test1 = \x -> case x of
                []     -> 42
                (a:as) -> a True
                
test2 = case [] of
            []     -> (\x -> x)
            (a:as) -> if a True then a else a
