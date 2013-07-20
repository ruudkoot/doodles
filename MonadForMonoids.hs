{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}

-- | Utility

flatten :: [[a]] -> [a]
flatten []   = []
flatten ([]:xss) = flatten xss
flatten ((x:xs):xss) = x : flatten (xs:xss)

mflatten :: Monoid m => m (m a) -> m a
mflatten ms | ms == empty = empty
            | 

-- | Monoids

class Monoid (m a) where
    empty :: m a
    embed :: a -> m a
    (+++) :: m a -> m a -> m a
    
instance Monoid [a] where
    empty   = []
    embed x = [x]
    m +++ n = m ++ n
    
-- | Category Theory

type I a = a
type (f :.: g) a = f (g a)
type f :=> g = forall a. f a -> g a
    
class Functor t => MONAD (t :: * -> *) where
    unit :: I :=> t
    mult :: t :.: t :=> t
    
instance MONAD [] where
    unit x = [x]
    mult = flatten
    
instance Monoid (m a) => MONAD m where
    unit x = embed x
    mult x = mflatten x

