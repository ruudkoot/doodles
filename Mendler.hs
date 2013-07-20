{-# LANGUAGE GADTs, KindSignatures, Rank2Types, NPlusKPatterns #-}

module Main where

import Prelude hiding (succ)
         
-- | Type-level fixpoints
         
newtype Mu0 (f :: *        -> *       )   = In0 { out0 :: f (Mu0 f)   }
newtype Mu1 (f :: (* -> *) -> (* -> *)) i = In1 { out1 :: f (Mu1 f) i }

-- | (Mendler-style) cata-/histomorphisms

cata   :: Functor f =>                                                          (f a   -> a  )  -> Mu0 f   -> a
mcata0 ::              (forall r  .                   (          r   -> a  ) -> (f r   -> a  )) -> Mu0 f   -> a
mcata1 ::              (forall r i.                   (forall i. r i -> a i) -> (f r i -> a i)) -> Mu1 f i -> a i
mhist0 ::              (forall r  . (r   -> f r  ) -> (          r   -> a  ) -> (f r   -> a  )) -> Mu0 f   -> a
mhist1 ::              (forall r i. (r i -> f r i) -> (forall i. r i -> a i) -> (f r i -> a i)) -> Mu1 f i -> a i
cata   phi (In0 x) = phi      (fmap (cata   phi) x)
mcata0 phi (In0 x) = phi            (mcata0 phi) x
mcata1 phi (In1 x) = phi            (mcata1 phi) x
mhist0 phi (In0 x) = phi out0       (mhist0 phi) x
mhist1 phi (In1 x) = phi out1       (mhist1 phi) x


-- | Lists / length

data L p r = N | C p r
type List p = Mu0 (L p)
nil       = In0 N
cons x xs = In0 (C x xs)

instance Functor (L p) where
    fmap f N        = N
    fmap f (C x xs) = C x (f xs)
    
len_c :: List p -> Int
len_c = cata phi where
    phi N           = 0
    phi (C x xslen) = 1 + xslen

len_m :: List p -> Int
len_m = mcata0 phi where
    phi :: (r -> Int) -> L p r -> Int
    phi len N        = 0
    phi len (C x xs) = 1 + len xs    

-- | Natural numbers / Fibonacci
         
        
data N r = Z | S r
type Nat = Mu0 N
zero   = In0 Z
succ n = In0 (S n)

int2nat 0 = zero
int2nat n = succ (int2nat (n-1))

fib :: Int -> Int
fib 0       = 0
fib (n + 1) = case n of
                0      -> 1
                n' + 1 -> fib n + fib n'

fib_m :: Nat -> Int
fib_m = mhist0 phi where
    phi :: (r -> N r) -> (r -> Int) -> N r -> Int
    phi out fib Z = 0
    phi out fib (S n) = case out n of
                            Z    -> 1
                            S n' -> fib n + fib n'

-- | Bush data type

data Bush i = NB | CB i (Bush (Bush i))

bs :: Bush Int
bs = CB 1 bs'
bs' :: Bush (Bush Int)
bs' = CB (CB 2 NB) bs''
bs'' :: Bush (Bush (Bush Int))
bs'' = CB (CB (CB 3 NB) (CB (CB (CB 4 NB) NB) NB)) NB

bsum :: Bush i -> (i -> Int) -> Int
bsum NB = (\f -> 0)
bsum (CB x xs) = (\f -> f x + bsum xs (\ys -> bsum ys f))

newtype Ret i = Ret { unRet :: (i -> Int) -> Int }

bsum' :: Bush i -> Ret i
bsum' NB = Ret (\f -> 0)
bsum' (CB x xs) = Ret (\f -> f x + bsum'' xs (\ys -> bsum'' ys f))
    where bsum'' :: Bush i -> (i -> Int) -> Int
          bsum'' = unRet . bsum'
          
-- | Indexed datatypes

data Z
data S i
          
data Vec p i where
    NV ::                 Vec p  Z
    CV :: p -> Vec i p -> Vec p (S i)
    


