module ABriefOverviewOfAgda where

-- 1  Introduction

-- 2  Agda Features

-- 3  Agda and some Related Langauges

-- 4  Example: Equational Proofs in Commutative Monoids

module Example where

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  prf : ∀ n m → (n + m) + n ≡ m + (n + n)
  prf = {!!}

  open import Data.Fin

  data Expr n : Set where
    var  : Fin n           → Expr n
    _⊕_  : Expr n → Expr n → Expr n
    zero :                   Expr n

  open import Data.Vec

  NF : ℕ → Set
  NF n = Vec ℕ n

  eval : ∀ {n} → Expr n → NF n
  eval = {!!}

  reify : ∀ {n} → NF n → Expr n
  reify = {!!}

  open import Function

  norm : ∀ {n} → Expr n → Expr n
  norm = reify ∘ eval

  data Eqn n : Set where
    _==_ : Expr n → Expr n → Eqn n

  build = ?

  eqn₁ : Eqn 2
  eqn₁ = build 2 (λ a b → (((a ⊕ b) ⊕ a) == (b ⊕ (a ⊕ a))))

  simpl : ∀ {n} → Eqn n → Eqn n
  simpl (e₁ == e₂) = norm e₁ == norm e₂

  open import Algebra

  module Semantics (CM : CommutativeMonoid) where

    open CommutativeMonoid CM renaming (Carrier to C)

    Env : ℕ → Set
    Env n = Vec C n

    ⟦_⟧ : ∀ {n} → Expr n → Env n → C
    ⟦ var i ⟧ ρ = lookup i ρ
    ⟦ a ⊕ b ⟧ ρ = ⟦ a ⟧ ρ • ⟦ b ⟧ ρ
    ⟦ zero ⟧  ρ = ε

    Prf : ∀ {n} → Eqn n → Env n → Set
    Prf (e₁ == e₂) ρ = ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ

    sound : ∀ {n} (e : Expr n) ρ → ⟦ e ⟧ ρ ≈ ⟦ norm e ⟧ ρ
    sound = ?

  prove : ∀ {n} (eqn : Eqn n) ρ → Prf (simpl eqn) ρ → Prf eqn ρ
  prove = ?

  prf : ∀ n m → (n + m) + n ≡ m + (n + n)
  prf n m = prove eqn₁ (n ∷ m ∷ []) ≡-refl



  