{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}

module Cat where

-- | Isomorphism

type a   <->   b = (a ->   b, b ->   a)             -- isomorphism
type a  <:-:>  b = (a :->  b, b :->  a)             -- natural isomorphism?
type a <::-::> b = (a ::-> b, b ::-> a)

-- | Natural transformations

type f :-> g  = forall a.   f a   ->  g a           -- natural transformation
type l ::-> m = forall a b. l a b :-> m a b

naturality :: (Functor l, Functor m, Eq (l x -> m y))
                => (l :-> m) -> (x -> y) -> Bool
naturality h k = h . fmap k == fmap k . h

-- | Yoneda lemma

type Y f a = forall r. (a -> r) -> f r

yonedaLemma :: Functor f => Y f <:-:> f
yonedaLemma = (\f -> f id, flip fmap)
