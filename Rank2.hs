{-# LANGUAGE RankNTypes #-}

three, four :: Int
three = 3
four  = 4

pr :: (forall a. a -> a) -> Int
pr = \f -> if f False then f three else four
