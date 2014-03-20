module Vectors where

-- | Zipping lists of compatible shape

module List where

  open import Data.Product hiding (zip)

  data List (X : Set) : Set where
    ⟨⟩  :                List X
    _,_ : X → List X → List X

  infixr 4 _,_

  zip : {S T : Set} → List S → List T → List (S × T)
  zip ⟨⟩ ⟨⟩ = ⟨⟩
  zip (s , ss) (t , ts) = (s , t) , zip ss ts
  zip _      _      = ⟨⟩

module Nat where

  open List

  data ℕ : Set where
    zero :       ℕ
    suc  : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ   #-}
  {-# BUILTIN ZERO    zero #-}
  {-# BUILTIN SUC     suc  #-}

  length : {X : Set} → List X → ℕ
  length ⟨⟩       = zero
  length (x , xs) = suc (length xs)

-- | Vectors

module Vec where

  open Nat
  open import Data.Product hiding (zip)

  data Vec (X : Set) : ℕ → Set where
    ⟨⟩  : Vec X zero
    _,_ : {n : ℕ} → X → Vec X n → Vec X (suc n)

  zip : ∀{n S T} → Vec S n → Vec T n → Vec (S × T) n
  zip ⟨⟩       ⟨⟩       = ⟨⟩
  zip (s , ss) (t , ts) = (s , t) , zip ss ts

  vec : forall {n X} -> X -> Vec X n
  vec {zero} x = ⟨⟩
  vec {suc n} x = x , vec x

  vapp : forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
  vapp ⟨⟩ ⟨⟩ = ⟨⟩
  vapp (x , fs) (x₁ , ss) = x x₁ , vapp fs ss

  vmap : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
  vmap f ss = vapp (vec f) ss

  zip' : forall {n S T} -> Vec S n -> Vec T n -> Vec (S × T) n
  zip' ss ts = vapp (vapp (vec (\x y -> x , y)) ss) ts

  data Fin : ℕ -> Set where
    zero : {n : ℕ} -> Fin (suc n)
    suc : {n : ℕ} -> Fin n -> Fin (suc n)

  proj : forall {n X} -> Vec X n -> Fin n -> X
  proj ⟨⟩ ()
  proj (x , xs) zero = x
  proj (x , xs) (suc i) = proj xs i

  open import Function

  tabulate : forall {n X} -> (Fin n -> X) -> Vec X n
  tabulate {zero} f = ⟨⟩
  tabulate {suc n} f = f zero , tabulate (f ∘ suc)

-- | Applicative and Traversable Structure

module Applicative where

  open import Function

  record EndoFunctor (F : Set -> Set) : Set₁ where
    field
      map : forall {S T} -> (S -> T) -> F S -> F T

  open EndoFunctor {{...}} public

  record Applicative (F : Set -> Set) : Set₁ where
    infixl 2 _⊛_
    field
      pure : forall {X} -> X -> F X
      _⊛_ : forall {S T} -> F (S -> T) -> F S -> F T
    applicativeEndoFunctor : EndoFunctor F
    applicativeEndoFunctor = record {map = _⊛_ ∘ pure}

  open Applicative {{...}} public

  open Vec

  applicativeVec : forall {n} -> Applicative λ X → Vec X n
  applicativeVec = record {pure = vec; _⊛_ = vapp}

  endoFunctorVec : forall {n} -> EndoFunctor λ X → Vec X n
  endoFunctorVec = applicativeEndoFunctor

  
  applicativeFun : forall {S} -> Applicative λ X -> S -> X
  applicativeFun = record
    { pure = λ x s -> x           -- K
    ; _⊛_ = λ f a s -> f s (a s)  -- S
    }

  record Monad (F : Set -> Set) : Set₁ where
    field
      return : forall {X} -> X -> F X
      _⟫=_   : forall {S T} -> F S -> (S -> F T) -> F T
    monadApplicative : Applicative F
    monadApplicative = record
      { pure = return
      ; _⊛_  = λ ff fs -> ff ⟫= λ f -> fs ⟫= λ s -> return (f s)
      }

  open Monad {{...}} public

  
