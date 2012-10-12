-- {-# LANGUAGE ScopedTypeVariables #-}

{-
-- Preserves the order of the complement
mapWithComplement :: (a -> [a] -> b) -> [a] -> [b]
mapWithComplement = mapWithComplement_ []
    where mapWithComplement_ :: [a] -> (a -> [a] -> b) -> [a] -> [b]
          mapWithComplement_ 
-}

-- Does not preserve the order of the complement
mapWithComplement' :: (a -> [a] -> b) -> [a] -> [b]
mapWithComplement' f = mapWithComplement_ []
    where -- mapWithComplement_ :: [a] -> [a] -> [b]
          mapWithComplement_ _  []     = []
          mapWithComplement_ ys (x:xs) = f x (ys ++ xs) : mapWithComplement_ (x:ys) xs
          
mapWithComplements :: (a -> [a] -> [a] -> b) -> [a] -> [b]
mapWithComplements f = mapWithComplements_ []
    where -- mapWithComplements_ :: [a] -> [a] -> [b]
          mapWithComplements_ _  _ []     = []
          mapWithComplements_ ys _ (x:xs) = f x ys xs : mapWithComplement_ (x:ys) xs
