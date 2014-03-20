{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

module Main where

-- | de Bruijn Indices

data Nat = O | S Nat
    deriving Show

data TmB where
    VarB :: Nat        -> TmB
    AppB :: TmB -> TmB -> TmB
    LamB :: TmB        -> TmB
    deriving Show

apB :: TmB
apB = LamB $ LamB $ VarB (S O) `AppB` VarB O

-- | Nested Abstract Syntax

data a :> v = Old a | New v
    deriving Show

bimap :: (a -> a') -> (v -> v') -> (a :> v) -> (a' :> v')
bimap f _ (Old x) = Old (f x)
bimap _ g (New x) = New (g x)

untag :: a :> a -> a
untag (Old x) = x
untag (New x) = x

type Succ a = a :> ()

data Zero where

data Tm a where
    Var :: a            -> Tm a
    App :: Tm a -> Tm a -> Tm a
    Lam :: Tm (Succ a)  -> Tm a
    deriving Show


