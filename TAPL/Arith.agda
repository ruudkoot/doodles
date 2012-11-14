module Arith where

open import Relation.Binary.Core

module ArithBool where

  data Term : Set where
    true : Term
    false : Term
    if_then_else_ : Term -> Term -> Term -> Term

  data Value : Set where
    true : Value
    false : Value

  data _⟶_ : Term -> Term -> Set where
    E-IfTrue : forall {t₂ t₃} -> if true then t₂ else t₃ ⟶ t₂
    E-IfFalse : forall {t₂ t₃} -> if false then t₂ else t₃ ⟶ t₃
    E-If : forall {t₁ t₁' t₂ t₃} -> t₁ ⟶ t₁' -> if t₁ then t₂ else t₃ ⟶ if t₁' then t₂ else t₃

  -- Theorem 3.5.4 [Determinacy of One-Step Evaluation]
  determinacy : (t : Term){t' t'' : Term} -> t ⟶ t' -> t ⟶ t'' → t' ≡ t''
  determinacy true                      ()           ()
  determinacy false                     ()           ()
  determinacy (if .true  then _ else _) E-IfTrue     E-IfTrue     = refl
  determinacy (if .true  then _ else _) E-IfTrue     (E-If ())
  determinacy (if .false then _ else _) E-IfFalse    E-IfFalse    = refl
  determinacy (if .false then _ else _) E-IfFalse    (E-If ())
  determinacy (if .true  then _ else _) (E-If ())    E-IfTrue
  determinacy (if .false then _ else _) (E-If ())    E-IfFalse
  determinacy (if t      then _ else _) (E-If t⟶t') (E-If t⟶t'') with determinacy t t⟶t' t⟶t'' 
  ... | refl = refl

module ArithBoolNat where

  data Term : Set where
    true : Term
    false : Term
    if_then_else_ : Term -> Term -> Term -> Term
    zero : Term
    succ : Term -> Term
    pred : Term -> Term
    iszero : Term -> Term

  data NumericValue : Set where
    zero : NumericValue
    succ : NumericValue -> NumericValue

  {-# BUILTIN NATURAL NumericValue #-}
  {-# BUILTIN ZERO zero #-}
  {-# BUILTIN SUC succ #-}

  data Value : Set where
    true : Value
    false : Value
    nv : NumericValue -> Value

  data _⟶_ : Term -> Term -> Set where
    E-IfTrue : forall {t₂ t₃} -> if true then t₂ else t₃ ⟶ t₂
    E-IfFalse : forall {t₂ t₃} -> if false then t₂ else t₃ ⟶ t₃
    E-If : forall {t₁ t₁' t₂ t₃} -> t₁ ⟶ t₁' -> if t₁ then t₂ else t₃ ⟶ if t₁' then t₂ else t₃
    E-Succ : forall {t₁ t₁'} -> t₁ ⟶ t₁' -> succ t₁ ⟶ succ t₁'
    E-PredZero : pred zero ⟶ zero
    E-PredSucc : forall {nv₁} -> pred (succ nv₁) ⟶ nv₁
    E-Pred : forall {t₁ t₁'} -> t₁ ⟶ t₁' -> pred t₁ ⟶ pred t₁'
    E-IszeroZero : iszero zero ⟶ true
    E-IszeroSucc : forall {nv₁} -> iszero (succ nv₁) ⟶ false
    E-IsZero : forall {t₁ t₁'} -> t₁ ⟶ t₁' -> iszero t₁ ⟶ iszero t₁'

  determinacy : (t : Term){t' t'' : Term} -> t ⟶ t' -> t ⟶ t'' → t' ≡ t''
  determinacy true () ()
  determinacy false () ()
  determinacy (if .true  then _  else _ ) E-IfTrue  E-IfTrue  = refl
  determinacy (if .true  then _  else _ ) E-IfTrue  (E-If ())
  determinacy (if .false then _  else _ ) E-IfFalse E-IfFalse = refl
  determinacy (if .false then _  else _ ) E-IfFalse (E-If ())
  determinacy (if .true  then _  else _ ) (E-If ()) E-IfTrue
  determinacy (if .false then _  else _ ) (E-If ()) E-IfFalse
  determinacy (if y      then y' else y0) (E-If y1) (E-If y2) with determinacy y y1 y2
  ... | refl = refl
  determinacy zero () ()
  determinacy (succ y) (E-Succ y') (E-Succ y0) with determinacy y y' y0
  ... | refl = refl
  determinacy (pred true) (E-Pred ()) _
  determinacy (pred false) (E-Pred ()) _
  determinacy (pred (if a then b else c)) x y = {!!}
  determinacy (pred zero) E-PredZero E-PredZero = refl
  determinacy (pred zero) E-PredZero (E-Pred ())
  determinacy (pred zero) (E-Pred ()) E-PredZero
  determinacy (pred zero) (E-Pred y) (E-Pred y') with determinacy zero y y'
  ... | refl = refl
  determinacy (pred (succ y)) x y' = {!!}
  determinacy (pred (pred y)) x y' = {!!}
  determinacy (pred (iszero y)) x y' = {!!}
  determinacy (iszero true) (E-IsZero ()) y'
  determinacy (iszero false) (E-IsZero ()) y'
  determinacy (iszero (if y then y' else y0)) x y1 = {!!}
  determinacy (iszero zero) E-IszeroZero E-IszeroZero = refl
  determinacy (iszero zero) E-IszeroZero (E-IsZero ())
  determinacy (iszero zero) (E-IsZero ()) E-IszeroZero
  determinacy (iszero zero) (E-IsZero y) (E-IsZero y') with determinacy  zero y y'
  ... | refl = refl
  determinacy (iszero (succ y)) x y' = {!!}
  determinacy (iszero (pred y)) x y' = {!!}
  determinacy (iszero (iszero y)) x y' = {!!}

  data Univ : Set where
    t : Univ
    v : Univ
    nv : Univ

  El : Univ -> Set
  El t  = Term
  El v  = Value
  El nv = NumericValue
{-
  data _⇓_ : Term -> Term -> Set where
    B-Value-True : true ⇓ true
    B-Value-False : false ⇓ false
    B-Value-Zero : zero ⇓ zero
    B-Value-Zero : 
-}