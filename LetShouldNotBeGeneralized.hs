--{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs, KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-} -- (6.10, 6.12)

module Main where

--f :: forall a. a -> ((a, Bool), (a, Char))
f x = let --g :: forall b. b -> (a, b)
          g y = (x, y) in (g True, g 'a')

--h :: (forall a. a -> b) -> (b, b)
--h x = let g y = x y in (g True, g 'a')


k x a b = let g y = y x in (g a, g b)

f2 :: forall a. a -> ((a, Bool), (a, Bool))
f2 x = let g :: forall b. Eq b => b -> (a, Bool)
           g y = (x, y==y) in (g True, g 'a')
           
f3 :: forall a. Eq a => a -> ((Bool, Bool), (Bool, Char))
f3 x = let g :: forall b. b -> (Bool, b)
           g y = (x==x, y) in (g True, g 'a')
           


{-
data T :: * -> * where
    T1 :: Int -> T Bool
    T2 :: T a

fr :: forall a. a -> T a -> Bool
fr x y = let gr :: forall b. (a ~ Bool) => b -> Bool
             gr z = not x
         in case y of
           T1 _ -> gr ()
           T2   -> True
-}

