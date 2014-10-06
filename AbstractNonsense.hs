{-# LANGUAGE NoImplicitPrelude     #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}

module Main where

-- | Prelude

undefined = undefined

-- | Functions

class IsFunction (arr :: * -> * -> *) where
    lambda :: (a -> b) -> a `arr` b
    (@@)   :: a `arr` b -> a -> b

instance IsFunction (->) where
    lambda = id
    f @@ x = f x
    
infixl 9 @@

-- | Categories

class Category arr where
    id :: a `arr` a
    (.) :: b `arr` c -> a `arr` b -> a `arr` c
    
instance Category (->) where
    id      x = x
    (f . g) x = f (g x)

{-
instance Category arr => Category (Op arr) where
    id x      = undefined
    (f . g) x = undefined
-}

-- | Opposites

newtype Op arr a b = Op { op :: b `arr` a }

type (<~) = Op (->)

-- | Bifunctors

type Covariant     = (->)
type Contravariant = (<~)

class Bifunctor (f :: * -> * -> *) where
    type Arg1 f :: * -> * -> *
    type Arg1 f = Covariant
    type Arg2 f :: * -> * -> *
    type Arg2 f = Covariant
    bimap :: Arg1 f a a' -> Arg2 f b b' -> f a b -> f a' b'

instance Bifunctor (,) where
    bimap f g (x , y) = (f x , g y)

instance Bifunctor (->) where
    type Arg1 (->) = Contravariant
    bimap (op -> i) o f = o . f . i

-- * boxed arrow

data (:->) a b = Arr { arr :: a -> b }

infixr 9 :->

-- {#- LANGUAGE OverloadedFunctions #-}
instance IsFunction (:->) where
    lambda          = Arr
    (arr -> f) @@ x = f x

instance Category (:->) where
    id                      = Arr id
    (arr -> f) . (arr -> g) = Arr (f . g)

instance Bifunctor (:->) where
    type Arg1 (:->) = Contravariant
    bimap (op -> i) o (arr -> f) = Arr (o . f . i)

-- * "set-theoretic" functions

-- * stateful functions

-- * non-standard kinds

-- | Bimonads

data Or a b = None | This a | That b | Both a b

-- According to Sjoerd Visscher. This seems like a sensible definition to handle
-- Both (Both a b) (Both c d). Programmer needs to make a choice here. I suspect
-- there are more ways to generalize this. nLab also notes this ("Hopf monad"):
-- A bimonad is both a monad and a comonad.
class (Bifunctor m, Bifunctor n) => Bimonad m n where
    bireturn :: (a , b) -> (m a b , n a b)
    bijoin   :: (m (m a b) (n a b) , n (m a b) (n a b)) -> (m a b , n a b)
    (>>==)   :: (m a b , n a b) -> (a -> m a' b' , b -> n a' b') -> (m a' b' , n a' b') 
    (x , y) >>== (f , g) = bijoin (bimap f g x) (bimap f g y)

instance Bifunctor Or where
    bimap _ _ (None    ) = None
    bimap f _ (This x  ) = This (f x)
    bimap _ g (That   y) = That       (g y)
    bimap f g (Both x y) = Both (f x) (g y)

instance Bimonad Or Or where
    bireturn (x , y) = (This x , That y)
    bijoin   (x , y) = (bijoin1 x , bijoin2 y)
        where   bijoin1 (None    ) = None
                bijoin1 (This x  ) = x
                bijoin1 (That   y) = None
                bijoin1 (Both x y) = x

                bijoin2 (None    ) = None
                bijoin2 (This x  ) = None
                bijoin2 (That   y) = y
                bijoin2 (Both x y) = y
    
    
-- * non-symmetric instance? mixed-arity instance?

-- * tree bimonad
-- * free bimonad
