{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}

module ClownsAndJokers where

import Prelude hiding (Functor(..))

-- 1  Introduction

data Expr = Val Int | Add Expr Expr

eval1 :: Expr -> Int
eval1 (Val i)     = i
eval1 (Add e1 e2) = eval1 e1 + eval1 e2

data a :|: b = L a | R b

type Stack = [Expr :|: Int]

eval :: Expr -> Int
eval e = load e []

load :: Expr -> Stack -> Int
load (Val i )    stk = unload i stk
load (Add e1 e2) stk = load e1 (L e2 : stk)

unload :: Int -> Stack -> Int
unload v []            = v
unload v1 (L e2 : stk) = load e2 (R v1 : stk)
unload v2 (R v1 : stk) = unload (v1 + v2) stk
  
-- 2  Polynomial Functors and Bifunctors

data K1 a      x = K1 a
data Id        x = Id x
data (p :+: q) x = L1 (p x) | R1 (q x)
data (p :*: q) x = p x :*: q x

type One = K1 ()

type MaybeF = One :+: Id
nothing = L1 (K1 ())
just x  = R1 (Id x)

class Functor p where
  fmap :: (s -> t) -> p s -> p t
  
instance Functor (K1 a) where
  fmap f (K1 a) = K1 a
  
instance Functor Id where
  fmap f (Id s) = Id (f s)
  
instance (Functor p, Functor q) => Functor (p :+: q) where
  fmap f (L1 p) = L1 (fmap f p)
  fmap f (R1 q) = R1 (fmap f q)
  
instance (Functor p, Functor q) => Functor (p :*: q) where
  fmap f (p :*: q) = fmap f p :*: fmap f q
  
-- 2.1  Datatypes as Fixpoints of Polynomial Functors
  
type ExprP = K1 Int :+: (Id :*: Id)
valP i     = L1 (K1 i)
addP e1 e2 = R1 (Id e1 :*: Id e2)

data Mu p = In (p (Mu p))

type Expr2 = Mu ExprP
val2 i     = In (valP i)
add2 e1 e2 = In (addP e1 e2)

cata :: Functor p => (p v -> v) -> Mu p -> v
cata phi (In p) = phi (fmap (cata phi) p)

eval2 :: Mu ExprP -> Int
eval2 = cata phi where
  phi (L1 (K1 i)) = i
  phi (R1 (Id v1 :*: Id v2)) = v1 + v2
  
-- 2.2  Polynomial Bifunctors

data K2 a  x y = K2 a
data Fst x y = Fst x
data Snd x y = Snd y
data (p :++: q) x y = L2 (p x y) | R2 (q x y)
data (p :**: q) x y = p x y :**: q x y
type I2 = K2 ()

class Bifunctor (p :: * -> * -> *) where
  bimap :: (s1 -> t1) -> (s2 -> t2) -> p s1 s2 -> p t1 t2
  
instance Bifunctor (K2 a) where
  bimap f g (K2 a) = K2 a
  
instance Bifunctor Fst where
  bimap f g (Fst x) = Fst (f x)
  
instance Bifunctor Snd where
  bimap f g (Snd y) = Snd (g y)

instance (Bifunctor p, Bifunctor q) => Bifunctor (p :++: q) where
  bimap f g (L2 p) = L2 (bimap f g p)
  bimap f g (R2 q) = R2 (bimap f g q)
  
instance (Bifunctor p, Bifunctor q) => Bifunctor (p :**: q) where
  bimap f g (p :**: q) = bimap f g p :**: bimap f g q
  
-- 2.3  Nothing is Missing

data Zero

refute :: Zero -> a
refute x = x `seq` error "we never get this far"

inflate :: Functor p => p Zero -> p x
inflate = fmap refute

type O1 = K1 Zero
type O2 = K2 Zero

-- 3.  Clowns, Jokers and Dissection

newtype AllClowns p c j = AllClowns (p c)

instance Functor f => Bifunctor (AllClowns f) where
  bimap f g (AllClowns pc) = AllClowns (fmap f pc)
  
newtype AllJokers p c j = AllJokers (p j)

instance Functor f => Bifunctor (AllJokers f) where
  bimap f g (AllJokers pj) = AllJokers (fmap g pj)
  
class (Functor p, Bifunctor p'') => Diss p p'' | p -> p'' where
  right :: p j :|: (p'' c j, c) -> (j, p'' c j) :|: p c
  plug :: x -> p'' x x -> p x

instance Diss (K1 a) O2 where
  right (L (K1 a)   ) = R (K1 a)
  right (R (K2 z, c)) = refute z
  
  plug x (K2 z) = refute z

instance Diss Id     I2 where
  right (L (Id j)    ) = L (j, K2 ())
  right (R (K2 (), c)) = R (Id c)
  
  plug x (K2 ()) = Id x
  
instance (Diss p p'', Diss q q'') 
         => Diss (p :+: q) (p'' :++: q'') where
  right (L (L1 pj)) = mindp (right (L pj))
  right (L (R1 qj)) = mindq (right (L qj))
  right (R (L2 pd, c)) = mindp (right (R (pd, c)))
  right (R (R2 qd, c)) = mindq (right (R (qd, c)))
  
  plug x (L2 pd) = L1 (plug x pd)
  plug x (R2 qd) = R1 (plug x qd)

mindp (L (j, pd)) = L (j, L2 pd)
mindp (R pc)      = R (L1 pc)
mindq (L (j, qd)) = L (j, R2 qd)
mindq (R qc)      = R (R1 qc)

instance (Diss p p'', Diss q q'') 
         => Diss (p :*: q) ((p'' :**: AllJokers q) :++: (AllClowns p :**: q'')) where
  right (L (pj :*: qj))                    = mindp' (right (L pj)     ) qj
  right (R (L2 (pd :**: AllJokers qj), c)) = mindp' (right (R (pd, c))) qj
  right (R (R2 (AllClowns pc :**: qd), c)) = mindq' pc (right (R (qd, c)))
  
  plug x (L2 (pd :**: AllJokers qx)) = (plug x pd :*: qx)
  plug x (R2 (AllClowns px :**: qd)) = (px :*: plug x qd)

mindp' (L (j, pd)) qj = L (j, L2 (pd :**: AllJokers qj))
mindp' (R pc)      qj = mindq' pc (right (L qj))
mindq' pc (L (j, qd)) = L (j, R2 (AllClowns pc :**: qd))
mindq' pc (R qc)      = R (pc :*: qc)
  
-- 4.  How to Creep Gradually to the Right

tmap :: Diss p p'' => (s -> t) -> p s -> p t
tmap f ps = continue (right (L ps)) where
  continue (L (s, pd)) = continue (right (R (pd, f s)))
  continue (R pt)      = pt

-- 4.1  Tail-Recursive Catamorphism

tcata :: Diss p p'' => (p v -> v) -> Mu p -> v
tcata phi l = load' phi l []

load' :: Diss p p'' => (p v -> v) -> Mu p -> [p'' v (Mu p)] -> v
load' phi (In pt) stk = next phi (right (L pt)) stk

next :: Diss p p'' => (p v -> v) -> (Mu p, p'' v (Mu p)) :|: p v -> [p'' v (Mu p)] -> v
next phi (L (t, pd)) stk = load' phi t (pd : stk)
next phi (R pv)      stk = unload' phi (phi pv) stk

unload' :: Diss p p'' => (p v -> v) -> v -> [p'' v (Mu p)] -> v
unload' phi v (pd : stk) = next phi (right (R (pd, v))) stk
unload' phi v []         = v

eval3 :: Mu ExprP -> Int
eval3 = tcata phi where
  phi (L1 (K1 i))            = i
  phi (R1 (Id v1 :*: Id v2)) = v1 + v2
  
expr = add2 (val2 13) (add2 (val2 42) (val2 666))
test = eval3 expr

-- 5.  Derivative Derived by Diagonal Dissection

-- 5.1  Plugging In

-- 5.2  Zipping Around

zUp , zDown, zLeft, zRight :: Diss p p'' => (Mu p, [p'' (Mu p) (Mu p)]) -> Maybe (Mu p, [p'' (Mu p) (Mu p)])

zUp (t, []) = Nothing
zUp (t, pd : pds) = Just (In (plug t pd), pds)

zDown (In pt, pds) = case right (L pt) of
  L (t, pd) -> Just (t, pd : pds)
  R _       -> Nothing
  
zRight (t, []) = Nothing
zRight (t :: Mu p, pd : pds) = case right (R (pd, t)) of
  L (t', pd') -> Just (t', pd' : pds)
  R (_ :: p (Mu p)) -> Nothing
  
zLeft = undefined

-- 6. Division: No Clowns!

divide :: Diss p p'' => p x -> (x, p'' Zero x) :|: p Zero
divide px = right (L px)

inflateFst :: Bifunctor p => p Zero y -> p x y
inflateFst = bimap refute id

unite :: Diss p p'' => (x, p'' Zero x) :|: p Zero -> p x
unite (L (x, pl)) = plug x (inflateFst pl)
unite (R pz)      = inflate pz

-- 7.  Generic Generalisation

-- 7.1  Free Monads and Substitution

data Star p x = V x | C (p (Star p x))

instance Functor p => Monad (Star p) where
  return x = V x
  V x >>= s = s x
  C pt >>= s = C (fmap (>>= s) pt)
  
type S x = Maybe x

fishhook :: Functor p => Star p (S x) -> Star p x -> Star p x
t `fishhook` s = t >>= sigma where
  sigma Nothing = s
  sigma (Just x) = V x
  
-- 7.2  Indisriminate Stop-and-Search

harpoon :: (Functor p, PresEq p, Eq x) => Star p x -> Star p x -> Star p (S x)
t    `harpoon` s | t == s = V Nothing
V x  `harpoon` s          = V (Just x)
C pt `harpoon` s          = C (fmap (\x -> harpoon x s) pt)

instance (PresEq p, Eq x) => Eq (Star p x) where
  V x  == V y  = x == y
  C ps == C pt = pres (==) ps pt
  _    == _    = False

class PresEq p where
  pres :: (x -> x -> Bool) -> p x -> p x -> Bool
  
instance Eq a => PresEq (K1 a) where
  pres eq (K1 a1) (K1 a2) = a1 == a2
  
instance PresEq Id where
  pres eq (Id x1) (Id x2) = eq x1 x2
  
instance (PresEq p, PresEq q) => PresEq (p :+: q) where
  pres eq (L1 p1) (L1 p2) = pres eq p1 p2
  pres eq (R1 q1) (R1 q2) = pres eq q1 q2
  pres eq _       _       = False

instance (PresEq p, PresEq q) => PresEq (p :*: q) where
  pres eq (p1 :*: q1) (p2 :*: q2) = pres eq p1 p2 && pres eq q1 q2
  
-- 7.3  Hunting for a Needle in a Stack

data Leaf p x = VL x | CL (p Zero)

instance Functor ((:|:) a) where
  fmap f (L x) = L x
  fmap f (R x) = R (fmap f x)

leftOrLeaf :: Diss  p p'' => Star p x -> (Star p x, p'' Zero (Star p x)) :|: Leaf p x
leftOrLeaf (V x)  = R (VL x)
leftOrLeaf (C pt) = fmap CL (divide pt)

