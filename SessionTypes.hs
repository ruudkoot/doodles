{-# LANGUAGE TypeFamilies #-}

module SessionTypes where

-- | Session universe

data a :!: r = S0 a | S1 r
data a :?: r = R0 a | R1 r

data r :+: s = P0 r | P1 s
data r :&: s = N0 r | N1 s

data Eps     = Eps

-- | Dual session

type family Dual :: *

type instance Dual (a :!: r) =      a :?: Dual r
type instance Dual (a :?: r) =      a :!: Dual r
type instance Dual (r :+: s) = Dual r :&: Dual s
type instance Dual (r :&: s) = Dual r :+: Dual s
type instance Dual Eps       = Eps

-- | Session type

newtype Session s s' a = Session { unSession :: TChan a -> IO a }

data Cap e r

send :: a -> Session (Cap e (a :!: r)) (Cap e r) ()
send x = Session 


