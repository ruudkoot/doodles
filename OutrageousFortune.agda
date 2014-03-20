module OutrageousFortune where

open import Function
open import Data.Unit
open import Relation.Binary.PropositionalEquality

record Monad (M : Set₀ -> Set₁) : Set₁ where
  field return : {X : Set} -> X -> M X
        _>>=_  : {A B : Set} -> M A -> (A -> M B) -> M B
        left   : {A B : Set} -> {x : A} -> {k : A -> M B} -> ((return x) >>= k) ≡ (k x)

data Maybe (A : Set₀) : Set₁ where
  nothing : Maybe A
  just    : A -> Maybe A

maybeBind : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
maybeBind nothing  k = nothing
maybeBind (just x) k = k x

leftLaw : {A B : Set} -> {x : A} -> {k : A -> Maybe B} -> (maybeBind (just x)  k) ≡ (k x)
leftLaw = λ {A} {B} {x} {k} → {!!} 

maybeMonad : Monad Maybe
maybeMonad = record { return = λ x → just x
                    ; _>>=_  = maybeBind
                    ; left   = leftLaw
                    }

