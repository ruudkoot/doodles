{-# LANGUAGE Rank2Types     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Main where

{-
f :: Either a Int -> Either a Bool
f v@(Left _) = v
f (Right 0)  = Right False
f (Right _)  = Right True
-}

data Either' :: * -> * -> * where
    Left'  :: forall a b. a -> Either' a b
    Right' :: forall a b. b -> Either' a b

{-
f' :: Either' a Int -> Either' a Bool
f' v@(Left' _) = v
f' (Right' 0)  = Right' False
f' (Right' _)  = Right' True
-}

