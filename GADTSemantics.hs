{-# LANGUAGE GADTs, KindSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}

module Main where

data Term a = Const a
            | Pair (Term a) (Term a)
            | App (Term (a -> a)) (Term a)
         -- deriving Show

          
instance Functor Term where
    fmap f (Const a) = Const (f a)
    fmap f (Pair a b) = Pair (fmap f a) (fmap f b)
    --fmap f (App g x) = App (fmap () g) (fmap f x)

tt :: (b -> c) -> (a -> b) -> (a -> c)
tt f g = f . g


data GTerm :: * -> * where
    GConst :: a -> GTerm a
    GPair :: GTerm a -> GTerm b -> GTerm (a, b)
    GApp :: GTerm (a -> b) -> GTerm a -> GTerm b
    
instance Functor GTerm where
    fmap f t = case t of 
                GConst a   -> GConst (f a)
                -- GPair  a b -> GPair (fmap f a) (fmap f b)



data G f h a where
    GCon :: f (G f h) a -> G f h (h a)
    

-- | Higher-order functors
    
class HFunctor f where
    -- ffmap :: Functor g => (a -> b) -> f g a -> f g b
    hfmap :: NatTrans g h -> NatTrans (f g) (f h)
    
type NatTrans g h = forall a. g a -> h a

-- | Finite numbers

type Unit = ()

data Z
data S a

data BFin a where
    BFinCon :: Either Unit (BFin a) -> BFin (S a)


-- | Equality witness

data Eql a b where
    Refl :: Eql a a


-- | Left Kan extension

data Lan h g c = forall b. Lan (Eql (h b) c, g b)
              -- exists b. (h b = c, f (G f h) b)
              -- Lan h (f (G f h)) c

data K f h g a = forall b. HFunctor f => K (Eql (h b) a, f g b)

instance HFunctor (Lan h) where
    hfmap k (Lan (p, v)) = Lan (p, k v)
    
-- | Functor composition
    
newtype (HFunctor g, HFunctor h) => HComp g h k a = HComp (g (h k) a)

instance (HFunctor g, HFunctor h) => HFunctor (g `HComp` h) where
    hfmap k (HComp t) = HComp (hfmap (hfmap k) t)

instance HFunctor f => HFunctor (K f h) where
    hfmap k (K (p, v)) = K (p, hfmap k v)

data NG f h a where
    NGCon :: K f h (NG f h) a -> NG f h a
    
toLan :: (forall c. g c -> f (h c)) -> Lan h g c -> f c 
toLan s (Lan (Refl, v)) = s v 

fromLan :: (forall c. Lan h g c -> f c) -> g c -> f (h c) 
fromLan s t = s (Lan (Refl, t)) 

toK :: HFunctor f => (forall c. f g c -> k (h c)) -> K f h g c -> k c
toK s (K (Refl, v)) = s v

fromK :: HFunctor f => (forall c. K f h g c -> k c) -> f g c -> k (h c)
fromK s t = s (K (Refl, t))

newtype Mu f a = In (f (Mu f) a)

-- G f h = Mu (K f h)


