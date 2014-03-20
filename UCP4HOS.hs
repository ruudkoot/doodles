{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module UCP4HOS where

import Control.Applicative

type t^l = l t

data Exp name = Var      name
              | Lam      name  (Exp name)
              | App (Exp name) (Exp name)
              deriving Show

identity_FO :: Exp Integer
identity_FO = Lam 1
    (App (App (Lam 2 (Var 2)) (Lam 3 (Var 3)))
         (Var 1)
    )
    
class Ord name => Name name where
    bot :: name
    prime :: name -> name
    (#) :: name -> name -> name
    m # n | m >= n = m
          | n >  m = n
            
instance Name Integer where
    bot   = 0
    prime = succ
    
class (Name name, Applicative l) => HOI name l where
    var :: name -> (Exp name)^l
    var n = pure (Var n)
    app :: (Exp name)^l -> (Exp name)^l -> (Exp name)^l
    app e1 e2 = App <$> e1 <*> e2
    lam :: ((Exp name)^l -> (Exp name)^l) -> (Exp name)^l

identity :: HOI name l => Exp name ^ l
identity = lam (\x ->
    app (app (lam (\y -> y)) (lam (\z -> z)))
        x
    )

-- First attempt

newtype FA x = FA x deriving (Functor, Show)

instance Applicative FA where
    pure        x = FA     x
    FA f <*> FA x = FA $ f x

instance Name name => HOI name FA where
    lam f = Lam <$> n <*> f (var n)
        where n = undefined

-- Speculative naming

newtype SPEC x = SPEC x deriving (Functor, Show)

instance Applicative SPEC where
    pure            x = SPEC     x
    SPEC f <*> SPEC x = SPEC $ f x

instance Name name => HOI name SPEC where
    lam f = Lam <$> n' <*> f (pure (Var n'))
        where
            ph = var bot
            n  = max_V <$> f ph
            n' = prime n

max_V :: Name name => Exp name -> name
max_V (Var n)   = n
max_V (App f a) = max_V f # max_V a
max_V (Lam _ a) = max_V a
