-- Dependently Types Programming in Agda
-- Ulf Norell and James Chapman
-- 5 October 2012

-- 3  Programming Techniques

-- 3.1  Views

module Views where

-- Natural number parity

open import Data.Nat hiding (_≟_) renaming (ℕ to Nat)

data Parity : Nat -> Set where
  even : (k : Nat) -> Parity (k * 2)
  odd  : (k : Nat) -> Parity (1 + k * 2)

parity : (n : Nat) -> Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2))     | even k = odd k
parity (suc .(1 + k * 2)) | odd  k = even (suc k)

half : Nat -> Nat
half n with parity n
half .(k * 2)     | even k = k
half .(1 + k * 2) | odd  k = k

-- Finding an element in a list

open import Function   hiding (_$_)
open import Data.List               renaming (_∷_ to _::_)
open import Data.Bool  hiding (_≟_) renaming (T to isTrue)
open import Data.Unit  hiding (_≟_) renaming (⊤ to True)
open import Data.Empty              renaming (⊥ to False)

isFalse : Bool -> Set
isFalse = isTrue ∘ not

infixr 30 _:all:_
data All {A : Set}(P : A -> Set) : List A -> Set where
  all[]   : All P []
  _:all:_ : forall {x xs} -> P x -> All P xs -> All P (x :: xs)

satisfies : {A : Set} -> (A -> Bool) -> A -> Set
satisfies p x = isTrue (p x)

data Find {A : Set}(p : A -> Bool) : List A -> Set where
  found : (xs : List A)(y : A) -> satisfies p y -> (ys : List A) -> Find p (xs ++ y :: ys)
  not-found : forall {xs} -> All (satisfies (not ∘ p)) xs -> Find p xs

find₁ : {A : Set}(p : A -> Bool)(xs : List A) -> Find p xs
find₁ p [] = not-found all[]
find₁ p (x :: xs) with p x
... | true  = found [] x {!!} xs
... | false = {!!}

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) -> x == y -> Inspect x

inspect : {A : Set}(x : A) -> Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} -> x == true -> isTrue x
trueIsTrue refl = _

falseIsFalse : {x : Bool} -> x == false -> isFalse x
falseIsFalse refl = _

find : {A : Set}(p : A -> Bool)(xs : List A) -> Find p xs
find p [] = not-found all[]
find p (x :: xs) with inspect (p x)
... | it true  prf = found [] x (trueIsTrue prf) xs
... | it false prf with find p xs
find p (x :: ._) | it false _   | found xs y py ys = found (x :: xs) y py ys
find p (x :: xs) | it false prf | not-found npxs   = not-found (falseIsFalse prf :all: npxs)

-- Indexing into a list

data _∈_ {A : Set}(x : A) : List A -> Set where    -- needed additional parenthesis
  hd : forall {xs}   -> x ∈ (x :: xs)
  tl : forall {y xs} -> x ∈ xs -> x ∈ (y :: xs)

index : forall {A}{x : A}{xs} -> x ∈ xs -> Nat
index hd     = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : List A) : Nat -> Set where
  inside  : (x : A)(p : x ∈ xs) -> Lookup xs (index p)
  outside : (m : Nat) -> Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : Nat) -> Lookup xs n
[] ! n = outside n
(x :: xs) ! zero = inside x hd
(x :: xs) ! suc n with xs ! n
(x :: xs) ! suc .(index p)       | inside y p = inside y (tl p)
(x :: xs) ! suc .(length xs + n) | outside n  = outside n

-- A type checker for λ-calculus

infixr 30 _⟶_
data Type : Set where
  ı   : Type
  _⟶_ : Type -> Type -> Type

data Equal? : Type -> Type -> Set where
  yes : forall {τ} -> Equal? τ τ
  no  : forall {σ τ} -> Equal? σ τ

_≟_ : (σ τ : Type) -> Equal? σ τ
ı         ≟ ı       = yes
ı         ≟ (_ ⟶ _) = no
(_ ⟶ _)   ≟ ı       = no
(σ₁ ⟶ τ₁) ≟ (σ₂ ⟶ τ₂) with σ₁ ≟ σ₂ | τ₁ ≟ τ₂
(σ  ⟶ τ ) ≟ (.σ ⟶ .τ) | yes | yes = yes
(σ₁ ⟶ τ₁) ≟ (σ₂ ⟶ τ₂) | _   | _   = no

infixl 80 _$_
data Raw : Set where
  var : Nat -> Raw
  _$_ : Raw -> Raw -> Raw
  lam : Type -> Raw -> Raw

Cxt = List Type

data Term (Γ : Cxt) : Type -> Set where
  var : forall {τ} -> τ ∈ Γ -> Term Γ τ
  _$_ : forall {σ τ} -> Term Γ (σ ⟶ τ) -> Term Γ σ -> Term Γ τ
  lam : forall σ  {τ} -> Term (σ :: Γ) τ -> Term Γ (σ ⟶ τ)

erase : forall {Γ τ} -> Term Γ τ -> Raw
erase (var x)   = var (index x)
erase (t $ u)   = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

data Infer (Γ : Cxt) : Raw -> Set where
  ok  : (τ : Type)(t : Term Γ τ) -> Infer Γ (erase t)
  bad : {e : Raw} -> Infer Γ e