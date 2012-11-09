module DependentTypesAtWork where

-- 1  What are Dependent Types?

-- 2  Simply Types Polymorphic Functional Programming in Agda

-- 2.1  Truth Values

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

equiv : Bool -> Bool -> Bool
equiv true true = true
equiv true false = false
equiv false true = false
equiv false false = true

_||_ : Bool -> Bool -> Bool
true || _ = true
_ || true = true
_ || _ = false

_&&_ : Bool -> Bool -> Bool
false && _ = false
_ && false = false
_ && _ = true

_=>_ : Bool -> Bool -> Bool
false => _ = true
true => true = true
_ => _ = false

-- 2.2  Natural Numbers

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

pred : Nat -> Nat
pred zero = zero
pred (succ n) = n

_+_ : Nat -> Nat -> Nat
zero + m = m
succ n + m = succ (n + m)

_*_ : Nat -> Nat -> Nat
zero * n = zero
succ n * m = n * m + m

_-_ : Nat -> Nat -> Nat
zero - _ = zero
n      - zero   = n
succ n - succ m = n - m

_<_ : Nat -> Nat -> Bool
_      < zero = false
zero   < succ m = true
succ n < succ m = n < m

_≤_ : Nat -> Nat -> Bool
zero   ≤ _      = true
succ n ≤ zero   = false
succ n ≤ succ m = n ≤ m 

-- 2.3  Lambda Notation and Polymorphism

id₁ : (A : Set) -> A -> A
id₁ = \(A : Set) -> \(x : A) -> x


id₂ : (A : Set) -> A -> A
id₂ A x = x

K : (A B : Set) -> A -> B -> A
K _ _ x _ = x

S : (A B C : Set) -> (B -> C) -> (A -> B) -> A -> C  -- had to fix the type signature!
S _ _ _ f g x = f (g x)

-- 2.4  Imlicit Arguments

id₃ : {A : Set} -> A -> A
id₃ = \x -> x

id : {A : Set} -> A -> A
id x = x

example₁ = id zero
example₂ = id {Nat} zero
example₃ = id {_} zero

-- 2.5  Gödel System T

if_then_else_ : {C : Set} -> Bool -> C -> C -> C
if true then x else y = x
if false then x else y = y

natrec : {C : Set} -> C -> (Nat -> C -> C) -> Nat -> C
natrec p h zero = p
natrec p h (succ n) = h n (natrec p h n)

plus : Nat -> Nat -> Nat
plus n m = natrec m (\x y -> succ y) n

mult : Nat -> Nat -> Nat
mult n m = natrec zero (\x y -> plus y m) n

notT : Bool -> Bool
notT x = if x then false else true

equivT : Bool -> Bool -> Bool
equivT x y = if x then if y then true else false else if y then false else true

_||T_ : Bool -> Bool -> Bool
x ||T y = if x then true else if y then true else false

_&&T_ : Bool -> Bool -> Bool
x &&T y = if x then if y then true else false else false

_=>T_ : Bool -> Bool -> Bool
x =>T y = if x then if y then true else false else true

predT : Nat -> Nat
predT n = natrec zero (λ x y → x) n

_-T_ : Nat -> Nat -> Nat
n -T m = natrec {!!} {!!} {!!}

_<T_ : Nat -> Nat -> Bool
x <T y = {!!}

_≤T_ : Nat -> Nat -> Bool
x ≤T y = {!!}

-- 2.6  Parametrised Types

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter _ [] = []
filter p (x :: xs) with p x
... | true = x :: xs
... | false = xs

foldl : {A B : Set} -> (B -> A -> B) -> B -> List A -> B
foldl _⊕_ e []        = e
foldl _⊕_ e (x :: xs) = foldl _⊕_ (e ⊕ x) xs

listrec : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
listrec _⊕_ e [] = e
listrec _⊕_ e (x :: xs) = x ⊕ listrec _⊕_ e xs

-- A  More about the Agda System

-- Appendix A.1  Short Remaks on Agda Syntax

-- Postulates

postulate S₁ : Set
postulate one : Nat
postulate _<=_ : Nat -> Nat -> Set
postulate zero-lower-bound : (n : Nat) -> zero <= n

-- Precedence and Association of Infix Operators

infixr 60 _+_
infixr 70 _*_
-- infixr 40 _::_

-- Infix/Mix-fix Operator used in Prefix Position

if₁_then_else_ : {C : Set} -> Bool -> C -> C -> C
if₁_then_else_ true x y = x
if₁_then_else_ false x y = y

if₂_then_else_ : {C : Set} -> Bool -> C -> C -> C
if₂ true then x else y = x
if₂_then_else_ false x y = y

-- A.2  Data Type Definitions

data Bool₁ : Set where
  true : Bool₁
  false : Bool₁

-- Appendix A.3  Built-in Representation of Natural Numbers

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC succ #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

