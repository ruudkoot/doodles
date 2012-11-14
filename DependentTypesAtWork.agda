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

data _X_ (A B : Set) : Set where
  <_,_> : A -> B -> A X B

fst₁ : {A B : Set} -> A X B -> A
fst₁ < a , b > = a

snd₁ : {A B : Set} -> A X B -> B
snd₁ < a , b > = b

zip : {A B : Set} -> List A -> List B -> List (A X B)
zip [] [] = []
zip (x :: xs) (y :: ys) = < x , y > :: zip xs ys
zip _ _ = []

data _⊕_ (A B : Set) : Set where
  inl : A -> A ⊕ B
  inr : B -> A ⊕ B

case₁ : {A B C : Set} -> A ⊕ B -> (A -> C) -> (B -> C) -> C
case₁ (inl x) f _ = f x
case₁ (inr x) _ g = g x

-- 2.7  Termination-checking

div : Nat -> Nat -> Nat
div m n = if (m < n) then zero else succ (div (m - n) n)

-- 3  What can Dependent Types do for Us?

-- 3.1  Vectors: An Inductive Family

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (succ n)

vzip : {A B : Set} {n : Nat} -> Vec A n -> Vec B n -> Vec (A X B) n
vzip [] [] = []
vzip (x :: xs) (y :: ys) = < x , y > :: vzip xs ys

vhead : {A : Set} {n : Nat} -> Vec A (succ n) -> A
vhead (x :: _) = x

vtail : {A : Set} {n : Nat} -> Vec A (succ n) -> Vec A n
vtail (_ :: xs) = xs

vmap : {A B : Set} {n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

-- 3.2  Finite Sets

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (succ n)
  fsucc : {n : Nat} -> Fin n -> Fin (succ n)

_!_ : {A : Set} {n : Nat} -> Vec A n -> Fin n -> A
[] ! ()
(x :: xs) ! fzero = x
(x :: xs) ! fsucc i = xs ! i

_!!_ : {A : Set}{n : Nat} -> Vec A (succ n) -> Fin (succ n) -> A
(x :: xs) !! fzero   = x
(x :: xs) !! fsucc i with i 
(x :: xs) !! fsucc i | fzero   = xs !! i
(x :: xs) !! fsucc i | fsucc y = xs !! i

-- 3.3  Other Interesting Inductive Families

data DBTree (A : Set) : Nat -> Set where
  dlf : A -> DBTree A zero
  dnd : {n : Nat} -> DBTree A n -> DBTree A n -> DBTree A (succ n)

data HBTree (A : Set) : Nat -> Set where
  hbleaf : A -> HBTree A zero
  hbnode : {n : Nat} -> HBTree A n -> HBTree A n -> HBTree A (succ n)
  rsnode : {n : Nat} -> HBTree A n -> HBTree A (succ n) -> HBTree A (succ (succ n))
  lsnode : {n : Nat} -> HBTree A (succ n) -> HBTree A n -> HBTree A (succ (succ n))

example₄ = rsnode (hbleaf true) (hbnode (hbleaf false) (hbleaf true))

data _==_ {A : Set} : A -> A -> Set where
  refl : (x  : A) -> x == x

data Expr₁ : Nat -> Set where
  var : forall {n} -> Fin n -> Expr₁ n
  abs : forall {n} -> Expr₁ (succ n) -> Expr₁ n

example₅ : Expr₁ zero
example₅ = abs (abs (var (fsucc fzero)))

data Ty : Set where
  nat : Ty
  _⟶_ : Ty -> Ty -> Ty

data Expr₂ : Ty -> Set where
  nat : Nat -> Expr₂ nat
  abs : forall {τ} -> Expr₂ τ -> Expr₂ (nat ⟶ τ)             -- either make this more polymorphic
  app : forall {σ τ} -> Expr₂ (σ ⟶ τ) -> Expr₂ σ -> Expr₂ τ  -- or this one less

example₆ : Expr₂ nat
example₆ = app (abs (nat zero)) (nat zero)

-- 3.4  Type-checking Dependent Types

vzip₂ : {A B : Set} -> (n : Nat) -> Vec A n -> Vec B n -> Vec (A X B) n
vzip₂ zero [] [] = []
vzip₂ (succ n) (x :: xs) (y :: ys) = < x , y > :: vzip₂ n xs ys

-- Patern Matching with Dependent Types

vzip₃ : {A B : Set} -> (n : Nat) -> Vec A n -> Vec B n -> Vec (A X B) n  -- Type in PDF is wrongish
vzip₃ zero [] [] = []
vzip₃ (succ n) (_::_ .{n} x xs) (_::_ .{n} y ys) = < x , y > :: vzip₃ n xs ys

data Image {A B : Set} (f : A -> B) : B -> Set where
  im : (x : A) -> Image f (f x)

inv : {A B : Set} (f : A -> B) -> (y : B) -> Image f y -> A
inv f .(f x) (im x) = x

-- Normalisation During Type-checking

_++_ : {A : Set} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

_+'_ : Nat -> Nat -> Nat
n +' zero = n
n +' succ m = succ (n +' m)

postulate substEq : {A : Set} -> (m : Nat) -> (zero +' m) == m -> Vec A m -> Vec A (zero +' m)
postulate eq-z : (m : Nat) -> (zero +' m) == m

_++'_ : {A : Set} {n m : Nat } -> Vec A n -> Vec A m -> Vec A (n +' m)
_++'_ {m = m} []        ys = substEq m (eq-z m) ys
_++'_ {m = m} (x :: xs) ys = {!!}

-- 4  Propositions as Types

-- 4.1  Propositional Logic

data _&_ (A B : Set) : Set where
  ⟨_,_⟩ : A -> B -> A & B

_&₁_ : Set -> Set -> Set   -- Typo in the PDF
A &₁ B = A X B

fst : {A B : Set} -> A & B -> A
fst ⟨ a , b ⟩ = a

snd : {A B : Set} -> A & B -> B
snd ⟨ a , b ⟩ = b

data _\/_ (A B : Set) : Set where
  inl : A -> A ‌\/ B
  inr : B -> A \/ B

_+₁_ : Set -> Set -> Set
A +₁ B = A \/ B

case : {A B C : Set} -> A \/ B -> (A -> C) -> (B -> C) -> C
case (inl a) d e = d a
case (inr b) d e = e b

data True : Set where
  tt : True

data False : Set where

falseElim : {A : Set} -> False -> A
falseElim ()

Not : Set -> Set
Not A = A -> False

_==>_ : (A B : Set) -> Set
A ==> B = A -> B

data _==>'_ (A B : Set) : Set where
  fun : (A -> B) -> A ==>' B

apply : {A B : Set} -> A ==>' B -> A -> B
apply (fun f) a = f a

_<==>_ : Set -> Set -> Set
A <==> B = (A ==> B) & (B ==> A)

prop₁ : {P Q : Set} -> (P & Q) <==> (Q & P)
prop₁ = {!!}

-- 4.2  Predicate Logic

Forall : (A : Set) -> (B : A -> Set) -> Set
Forall A B = (x : A) -> B x

data Forall' (A : Set) (B : A -> Set) : Set where
  forallI : ((a : A) -> B a) -> Forall' A B

forallE : {A : Set}{B : A -> Set} -> Forall' A B -> (x : A) -> B x
forallE (forallI f) a = f a

data Exists (A : Set) (B : A -> Set) : Set where
  exists : (a : A) -> B a -> Exists A B

witness : {A : Set} {B : A -> Set} -> Exists A B -> A
witness (exists a b) = a

proof : {A : Set} {B : A -> Set} -> (p : Exists A B) -> B (witness p)
proof (exists a b) = b

case⊕ : {A B : Set} -> {C : A ‌\/ B -> Set} -> (z : A \/ B)
           -> ((x : A) -> C (inl x)) -> ((y : B) -> C (inr y)) -> C z
case⊕ (inl a) d e = d a
case⊕ (inr b) d e = e b

case0 : {C : False -> Set} -> (z : False) -> C z
case0 ()

case? = {!!}

proveSomeTautologies = {!!}

-- 4.3  Equality

data _≡_ {A : Set} : A -> A -> Set where
  refl : (a : A) -> a ≡ a

subst : {A : Set} -> {C : A -> Set} -> (a' a'' : A) -> a' ≡ a'' -> C a' -> C a''
subst .a .a (refl a) c = c

-- 4.4  Induction Princliples

natrec₂ : {C : Nat -> Set} -> (C zero) -> ((m : Nat) -> C m -> C (succ m)) -> (n : Nat) -> C n
natrec₂ p h zero = p
natrec₂ p h (succ n) = h n (natrec₂ p h n)

eq-succ₁ : {n m : Nat} -> n ≡ m -> succ n ≡ succ m
eq-succ₁ = {!!}

eq-succ₂ : {n m : Nat} -> n ≡ m -> succ n ≡ succ m
eq-succ₂ (refl m) = refl (succ m)

eq-plus-rec : (n m : Nat) -> (n + m) ≡ plus n m
eq-plus-rec n m = natrec₂ {\k -> k + m ≡ plus k m} (refl m) (\ k' ih -> eq-succ₁ ih) n

eq-mult-rec : (n m : Nat) -> (n + m) ≡ mult n m
eq-mult-rec n m = natrec₂ {λ k → k * m ≡ mult k m} {!!} {!!} {!!}

eq-plus : (n m : Nat) -> n + m ≡ plus n m
eq-plus zero m = refl m
eq-plus (succ n) m = eq-succ₂ (eq-plus n m)

eq-mult : (n m : Nat) -> n * m ≡ mult n m
eq-mult n m = {!!}

-- 5  Agda as a Programming Logic

-- 5.1  Binary Search Trees

postulate A : Set
postulate _<=_ : A -> A -> Set
postulate tot : (a b : A) -> (a <= b) \/‌ (b <= a)
postulate antisym : {a b : A} -> a <= b -> b <= a -> a == b
postulate reflex : (a : A) -> a <= a
postulate trans : {a b c : A} -> a <= b -> b <= c -> a <= c

-- Inserting an Element into a Binary Search Tree



-- A  More about the Agda System

-- Appendix A.1  Short Remaks on Agda Syntax

-- Postulates

postulate S₁ : Set
postulate one : Nat
postulate _<=₁_ : Nat -> Nat -> Set
postulate zero-lower-bound : (n : Nat) -> zero <=₁ n

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

