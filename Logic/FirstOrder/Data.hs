{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.FirstOrder.Data where

import Prelude hiding (not)

import Logic.Propositional.Standard.Data
import Logic.FirstOrder.Class

data Atom a
    = Var a
    | Predicate
    deriving (Eq, Show)

data Sentence a
    = Forall a (Sentence a)
    | Exists a (Sentence a)
    | P (Proposition Atom a)
    deriving (Eq, Show)

{-
instance IsSentence Sentence a where
    forall = Forall
    exists = Exists
    (/\)   = (:/\:)
    (\/)   = (:\/:)
    (==>)  = (:=>:)
    not    = Not
    var    = Var
-}
