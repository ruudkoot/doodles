{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.FirstOrder.Class where

class IsSentence sentence a where
    forall :: a -> sentence a -> sentence a
    exists :: a -> sentence a -> sentence a
    (/\)   :: sentence a -> sentence a -> sentence a
    (\/)   :: sentence a -> sentence a -> sentence a
    (==>)  :: sentence a -> sentence a -> sentence a
    not    :: sentence a -> sentence a
    var    :: a -> sentence a
