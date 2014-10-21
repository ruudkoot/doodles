{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.FirstOrderEq.Class (
    module Logic.FirstOrder.Class,
    IsSentenceEq(..)
) where

import Logic.FirstOrder.Class

class IsSentence sentence a => IsSentenceEq sentence a where
    (.=.) :: sentence a -> sentence a -> sentence a
