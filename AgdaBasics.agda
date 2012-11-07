-- Dependently Typed Programming in Agda
-- Ulf Norell and James Chapman
-- 5 October 2012

-- 1  Introduction

-- 2  Basics

module AgdaBasics where

-- 2.1  Datatypes and pattern matching

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool -> Bool
not true  = false
not false = true

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero  * m = zero
suc n * m = m + n * m    -- needs the infix declariation further down

_or_ : Bool -> Bool -> Bool
false or x = x
true  or _ = true

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix   5 if_then_else_

-- infixr 40 _::_    -- redefined in the exercises
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

data _★ (α : Set) : Set where
  ε : α ★
  _◃_ : α -> α ★ -> α ★

-- 2.2  Dependent functions

identity : (A : Set) -> A -> A
identity A x = x

zero' : Nat
zero' = identity Nat zero

apply : (A : Set)(B : A -> Set) -> ((x : A) -> B x) -> (a : A) -> B a
apply A B f a = f a

identity₂ : (A : Set) -> A -> A
identity₂ = \A x -> x

identity₃ : (A : Set) -> A -> A
identity₃ = \(A : Set)(x : A) -> x

identity₄ : (A : Set) -> A -> A
identity₄ = \(A : Set) x -> x

-- 2.3  Implicit arguments

id : {A : Set} -> A -> A
id x = x

true' : Bool
true' = id true

silly : {A : Set}{x : A} -> A
silly {_}{x} = x

false' : Bool
false' = silly {x = false}

one : Nat
one = identity _ (suc zero)

_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
      (f : {x : A}(y : B x) -> C x y)(g : (x : A) -> B x)
      (x : A) -> C x (g x)
(f ∘ g) x = f (g x)

plus-two = suc ∘ suc

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- 2.4  Datatype families

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x

-- Dot patterns

vmap : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f []        = []
vmap f (x :: xs) = f x :: vmap f xs

data Vec₂ (A : Set) : Nat -> Set where
  nil  : Vec₂ A zero
  cons : (n : Nat) -> A -> Vec₂ A n -> Vec₂ A (suc n)

vmap₂ : {A B : Set}(n : Nat) -> (A -> B) -> Vec₂ A n -> Vec₂ B n
vmap₂ .zero    f nil           = nil -- dot is optional here
vmap₂ .(suc n) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)
-- vmap₂ (suc n) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)
  -- "Repeated variables in left hand side: n
  --  when scope schcking the left-hand side
  --  vmap₂ (suc n) f (cons n x xs) in the definition of vmap₂"
-- vmap₂ (suc m) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)
  -- n != m of type Nat
  -- when checking that the pattern cons n x xs has type Vec₂ A (suc m)

vmap₃ : {A B : Set}(n : Nat) -> (A -> B) -> Vec₂ A n -> Vec₂ B n
vmap₃ zero    f nil            = nil
vmap₃ (suc n) f (cons .n x xs) = cons n (f x) (vmap₃ n f xs)

data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where
  im : (x : A) -> Image f ∋ f x

inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x
  -- Note: (f x) is not a valid pattern, but it is a valid dot pattern.

test₁ : Nat
test₁ = inv plus-two (suc (suc (suc (suc zero)))) (im _)

-- Absurd patterns

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

magic : {A : Set} -> Fin zero -> A
magic ()

data Empty : Set where
  empty : Fin zero -> Empty

magic' : {A : Set} -> Empty -> A
magic' (empty ())

_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
[]        ! ()
(x :: xs) ! fzero    = x
(x :: xs) ! (fsuc i) = xs ! i

tabulate : {n : Nat }{A : Set} -> (Fin n -> A) -> Vec A n
tabulate {zero}  f = []
tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)

-- 2.5  Programs as proofs

data   False : Set where
record True  : Set where

trivial : True
trivial = _  -- record{}

isTrue : Bool -> Set
isTrue true  = True
isTrue false = False

_<_ : Nat -> Nat -> Bool
_     < zero  = false
zero  < suc n = true
suc m < suc n = m < n

length : {A : Set} -> List A -> Nat
length []        = zero
length (x :: xs) = suc (length xs)

lookup : {A : Set}(xs : List A)(n : Nat) -> isTrue (n < length xs) -> A
lookup []        n       ()
lookup (x :: xs) zero    p  = x
lookup (x :: xs) (suc n) p  = lookup xs n p

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data _≤_ : Nat -> Nat -> Set where
  leq-zero : {n : Nat} -> zero ≤ n
  leq-suc  : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

leq-trans : {l m n : Nat} -> l ≤ m -> m ≤ n -> l ≤ n
leq-trans leq-zero    _           = leq-zero
leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)

-- 2.6  More on pattern matching

-- The with construct

min : Nat -> Nat -> Nat
min x y with x < y
min x y | true  = x
min x y | false = y

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) with p x
... | true  = x :: filter p xs
... | false = filter p xs

data _≠_ : Nat -> Nat -> Set where
  z≠s : {n : Nat} -> zero ≠ suc n
  s≠z : {n : Nat} -> suc n ≠ zero
  s≠s : {m n : Nat} -> m ≠ n -> suc m ≠ suc n

data Equal? (n m : Nat) : Set where
  eq  : n == m -> Equal? n m
  neq : n ≠ m  -> Equal? n m

equal? : (n m : Nat) -> Equal? n m
equal? zero     zero   = eq refl
equal? zero    (suc m) = neq z≠s
equal? (suc n) zero    = neq s≠z
equal? (suc n) (suc m) with equal? n m
equal? (suc n) (suc .n) | eq refl = eq refl
equal? (suc n) (suc m)  | neq p   = neq (s≠s p)

infix 20 _⊆_
data _⊆_ {A : Set} : List A -> List A -> Set where
  stop : [] ⊆ []
  drop : forall {xs y ys} -> xs ⊆ ys ->      xs ⊆ y :: ys
  keep : forall {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys

lem-filter : {A : Set}(p : A -> Bool)(xs : List A) -> filter p xs ⊆ xs
lem-filter p []        = stop
lem-filter p (x :: xs) with p x
... | true  = keep (lem-filter p xs)
... | false = drop (lem-filter p xs)

lem-plus-zero : (n : Nat) -> n + zero == n
lem-plus-zero zero = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
... | .n | refl = refl

-- 2.7  Modules

module M where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just    : A -> Maybe A

  maybe : {A B : Set} -> B -> (A -> B) -> Maybe A -> B
  maybe z f nothing  = z
  maybe z f (just x) = f x

module A where
  private
    internal : Nat
    internal = zero

  exported : Nat -> Nat
  exported n = n + internal

mapMaybe₁ : {A B : Set} -> (A -> B) -> M.Maybe A -> M.Maybe B
mapMaybe₁ f M.nothing  = M.nothing
mapMaybe₁ f (M.just x) = M.just (f x)

mapMaybe₂ : {A B : Set} -> (A -> B) -> M.Maybe A -> M.Maybe B
mapMaybe₂ f m = let open M in maybe nothing (just ∘ f) m

open M

mapMaybe₃ : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe₃ f m = maybe nothing (just ∘ f) m

open M hiding (maybe) renaming (Maybe to _option; nothing to none; just to some)

mapOption : {A B : Set} -> (A -> B) -> A option -> B option
mapOption f none     = none
mapOption f (some x) = some (f x)

mtrue : Maybe Bool
mtrue = mapOption not (just false)

-- Parameterised modules

module Sort (A : Set)(_<_ : A -> A -> Bool) where
  insert : A -> List A -> List A
  insert y [] = y :: []
  insert y (x :: xs) with x < y
  ... | true  = x :: insert y xs
  ... | false = y :: x :: xs

  sort : List A -> List A
  sort []        = []
  sort (x :: xs) = insert x (sort xs)

sort₁ : (A : Set)(_<_ : A -> A -> Bool) -> List A -> List A
sort₁ = Sort.sort

module SortNat = Sort Nat _<_

sort₂ : List Nat -> List Nat
sort₂ = SortNat.sort

open Sort Nat _<_ renaming (insert to insertNat; sort to sortNat)

module Lists (A : Set)(_<_ : A -> A -> Bool) where
  open Sort A _<_ public
  minimum : List A -> Maybe A
  minimum xs with sort xs
  ... | []      = nothing
  ... | y :: ys = just y

-- Importing modules from other files

import Logic using (_∧_; _∨_)

open import Logic hiding (Bool)

-- 2.8  Records

record Point : Set where
  field x : Nat
        y : Nat

mkPoint : Nat -> Nat -> Point
mkPoint a b = record{ x = a; y = b }

getX : Point -> Nat
getX = Point.x

abs² : Point -> Nat
abs² p = let open Point p in x * x + y * y

record Monad (M : Set -> Set) : Set1 where
  field
    return : {A : Set} -> A -> M A
    _>>=_  : {A B : Set} -> M A -> (A -> M B) -> M B

  mapM : {A B : Set} -> (A -> M B) -> List A -> M (List B)
  mapM f [] = return []
  mapM f (x :: xs) = f x       >>= \y  ->
                     mapM f xs >>= \ys ->
                     return (y :: ys)

mapM' : {M : Set -> Set} -> Monad M -> {A B : Set} -> (A -> M B) -> List A -> M (List B)
mapM' Mon f xs = Monad.mapM Mon f xs

-- 2.9  Exercises

-- Exercise 2.1. Matrix tranposition

Matrix : Set -> Nat -> Nat -> Set
Matrix A n m = Vec (Vec A n) m

vec : {n : Nat}{A : Set} -> A -> Vec A n
vec {zero}  x = []
vec {suc n} x = x :: vec x

infixl 90 _$_
_$_ : {n : Nat}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
fs        $ []        = []
(f :: fs) $ (x :: xs) = f x :: fs $ xs

zipWith₁ : {n : Nat}{A B C : Set} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zipWith₁ f []        []        = []
zipWith₁ f (x :: xs) (y :: ys) = f x y :: zipWith₁ f xs ys

transpose₁ : forall {A n m} -> Matrix A n m -> Matrix A m n
transpose₁ []          = vec []
transpose₁ (xs :: xss) = zipWith₁ _::_ xs (transpose₁ xss)

zipWith₂ : {n : Nat}{A B C : Set} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zipWith₂ f xs ys = (vec f $ xs) $ ys

transpose₂ : forall {A n m} -> Matrix A n m -> Matrix A m n
transpose₂ []          = vec []
transpose₂ (xs :: xss) = (vec _::_ $ xs) $ (transpose₂ xss)

-- Exercise 2.2. Vector lookup
                                                               -- needed some additional parentheses
lem-!-tab : forall {A n} (f : Fin n -> A)(i : Fin n) -> (tabulate f ! i) == f i
lem-!-tab f fzero    = refl
lem-!-tab f (fsuc i) = lem-!-tab (f ∘ fsuc) i

lem-tab-! : forall {A n} (xs : Vec A n) -> tabulate (_!_ xs) == xs
lem-tab-! []        = refl
lem-tab-! (x :: xs) with tabulate (_!_ xs) | lem-tab-! xs
... | .xs | refl = refl

-- Exercise 2.3. Sublists

⊆-refl : {A : Set}{xs : List A} -> xs ⊆ xs
⊆-refl {xs = []     } = stop
⊆-refl {xs = x :: xs} = keep ⊆-refl

⊆-trans : {A : Set}{xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
⊆-trans stop         stop         = stop
⊆-trans xs⊆ys        (drop ys⊆zs) = drop (⊆-trans xs⊆ys ys⊆zs)
⊆-trans (drop xs⊆ys) (keep ys⊆zs) = drop (⊆-trans xs⊆ys ys⊆zs)
⊆-trans (keep xs⊆ys) (keep ys⊆zs) = keep (⊆-trans xs⊆ys ys⊆zs)

infixr 30 _::_
data SubList {A : Set} : List A -> Set where
  [] : SubList []
  _::_ : forall x {xs} -> SubList xs -> SubList (x :: xs)
  skip : forall {x xs} -> SubList xs -> SubList (x :: xs)

forget : {A : Set}{xs : List A} -> SubList xs -> List A
forget []        = []
forget (x :: xs) = x :: forget xs
forget (skip xs) = forget xs

lem-forget : {A : Set}{xs : List A}(zs : SubList xs) -> forget zs ⊆ xs
lem-forget []        = stop
lem-forget (x :: xs) = keep (lem-forget xs)
lem-forget (skip xs) = drop (lem-forget xs)

filter' : {A : Set} -> (A -> Bool) -> (xs : List A) -> SubList xs
filter' p [] = []
filter' p (x :: xs) with p x
... | true  = x :: filter' p xs
... | false = skip (filter' p xs)

complement : {A : Set}{xs : List A} -> SubList xs -> SubList xs
complement               []        = []
complement               (_ :: ss) = skip (complement ss)
complement {xs = x :: _} (skip ss) = x :: complement ss

test₃ = filter' (\x -> x) (true :: true :: false :: true :: false :: false :: [])
test₄ = complement test₃

sublists : {A : Set}(xs : List A) -> List (SubList xs)
sublists [] = [] :: []
sublists (x :: xs) = map skip (sublists xs) ++ map (_::_ x) (sublists xs)

{-# BUILTIN NATURAL Nat #-}

test₅ = map forget (sublists (1 :: 2 :: 3 :: 4 :: []))
