{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ImpredicativeTypes  #-}

module NaturalTransformation where

-- | Natural transformations

data V2 a = V2 a a
data V3 a = V3 a a a

instance Functor V2 where
    fmap f (V2 x y)   = V2 (f x) (f y)
    
instance Functor V3 where
    fmap f (V3 x y z) = V3 (f x) (f y) (f z)

type a → b = a -> b                     -- morphism
type l ⇒ m = forall x. l x → m x        -- natural transformations

h :: V2 ⇒ V3
h (V2 x y) = V3 y x x

naturality :: (Functor l, Functor m, Eq (l x -> m y)) => (l ⇒ m) -> (x -> y) -> Bool
naturality h k = h . fmap k == fmap k . h

-- | Monads

type Id     x =      x
type O  f g x = f (g x)

class Functor f => Monad f where
    return :: Id      ⇒ f
    join   :: f `O` f ⇒ f

-- | Yoneda lemma

type a ≃ b = (a → b, b → a)             -- isomorphism
type a ≅ b = (a ⇒ b, b ⇒ a)             -- natural isomorphism

type Y  f a = forall r. (a → r) → f r    -- Yoneda embedding

yonedaLemma :: Functor f => Y f ≅ f
yonedaLemma = (\f -> f id, flip fmap)

-- | Godement calculus

type OO k l f x = O (k f) (l f) x
