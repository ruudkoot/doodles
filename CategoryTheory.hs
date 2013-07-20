{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CategoryTheory where

-- I

newtype I a = I a
            deriving Show

instance Functor I where
    fmap f (I a) = I (f a)

-- Option

data Option a = None
              | Some a
              deriving Show
              
instance Functor Option where
    fmap f None     = None
    fmap f (Some a) = Some (f a)
    
-- List

data List a = Nil
            | Cons a (List a)
            deriving Show
            
instance Functor List where
    fmap f Nil         = Nil
    fmap f (Cons a as) = Cons (f a) (fmap f as)

-- Natural transformations

type f :=>: g = forall a. f a -> g a

-- Composition
type (f :.: g) a = f (g a)

-- Monads

class Functor t => MyMonad t where
    unit :: I :=>: t                      -- return :: a -> t a
--  bind :: t b -> (I b -> t a) -> t a    -- (>>=) :: m a -> (a -> m b) -> m b
    mult :: t :.: t :=>: t                -- join :: m (m a) -> m a
    
instance MyMonad Option where
    unit (I x)           = Some x
    mult None            = None
    mult (Some None)     = None
    mult (Some (Some x)) = Some x
    
(>>==) :: (MyMonad t) => t a -> (I a -> t b) -> t b
x >>== f = mult ((fmap (f . I)) x)
