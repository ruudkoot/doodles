{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.FirstOrderEq.Data where

import Prelude hiding (not)
import Logic.FirstOrderEq.Class

data Sentence a
    = Forall a (Sentence a)
    | Exists a (Sentence a)
    | Sentence a :/\: Sentence a
    | Sentence a :\/: Sentence a
    | Sentence a :=>: Sentence a
    | Not (Sentence a)
    | Sentence a :=: Sentence a
    deriving (Eq, Show)
    
instance IsSentence Sentence a where
    forall = Forall
    exists = Exists
    (/\)   = (:/\:)
    (\/)   = (:\/:)
    (==>)  = (:=>:)
    not    = Not

instance IsSentenceEq Sentence a where
    (.=.) = (:=:)
