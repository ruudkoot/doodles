-- Dependently Types Programming in Agda
-- Ulf Norell and James Chapman
-- 5 October 2012

-- 3  Programming Techniques

-- 3.2  Universes

module Universes where

-- A familiar universe

data   False : Set where
record True  : Set where

data Bool : Set where
  true  : Bool
  false : Bool

isTrue : Bool -> Set
isTrue true  = True
isTrue false = False

infix  30 not_
infixr 25 _and_

not_ : Bool -> Bool
not true  = false
not false = true

_and_ : Bool -> Bool -> Bool
true  and x = x
false and _ = false

notNotId : (a : Bool) -> isTrue (not not a) -> isTrue a
notNotId true  p = p
notNotId false ()

andIntro : (a b : Bool) -> isTrue a -> isTrue b -> isTrue (a and b)
andIntro true  _ _  p = p
andIntro false _ () _

open import Data.Nat hiding (fold; compare) renaming (ℕ to Nat)

nonZero : Nat -> Bool
nonZero zero    = false
nonZero (suc _) = true

postulate _div_ : Nat -> (m : Nat){p : isTrue (nonZero m)} -> Nat

three = 16 div 5

-- Universes for generic programming

data Functor : Set1 where
  |Id|  : Functor
  |K|   : Set -> Functor
  _|+|_ : Functor -> Functor -> Functor
  _|x|_ : Functor -> Functor -> Functor

data _⊕_ (A B : Set) : Set where
  inl : A -> A ⊕ B
  inr : B -> A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 50 _|+|_ _⊕_
infixr 60 _|x|_ _×_

[_] : Functor -> Set -> Set
[ |Id|    ] X = X
[ |K| A   ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |x| G ] X = [ F ] X × [ G ] X

map : (F : Functor){X Y : Set} -> (X -> Y) -> [ F ] X -> [ F ] Y
map |Id|      f x       = f x
map (|K| A)   f c       = c
map (F |+| G) f (inl x) = inl (map F f x)
map (F |+| G) f (inr y) = inr (map G f y)
map (F |x| G) f (x , y) = map F f x , map G f y

data μ_ (F : Functor) : Set where
  <_> : [ F ] (μ F) -> μ F

-- fold : (F : Functor){A : Set} -> ([ F ] A -> A) -> μ F -> A
-- fold F φ < x > = φ (map F (fold F φ) x)

mapFold : forall {X} F G -> ([ G ] X -> X) -> [ F ] (μ G) -> [ F ] X
mapFold |Id|        G φ < x >   = φ (mapFold G G φ x)
mapFold (|K| A)     G φ c       = c
mapFold (F₁ |+| F₂) G φ (inl x) = inl (mapFold F₁ G φ x)
mapFold (F₁ |+| F₂) G φ (inr y) = inr (mapFold F₂ G φ y)
mapFold (F₁ |x| F₂) G φ (x , y) = mapFold F₁ G φ x , mapFold F₂ G φ y

fold : {F : Functor}{A : Set} -> ([ F ] A -> A) -> μ F -> A
fold {F} φ < x > = φ (mapFold F F φ x)

NatF = |K| True |+| |Id|
NAT  = μ NatF

Z : NAT
Z = < inl _ >

S : NAT -> NAT
S n = < inr n >

ListF = \A -> |K| True |+| |K| A |x| |Id|
LIST  = \A -> μ (ListF A)

nil : {A : Set} -> LIST A
nil = < inl _ >

cons : {A : Set} -> A -> LIST A -> LIST A
cons x xs = < inr (x , xs) >

[_||_] : {A B C : Set} -> (A -> C) -> (B -> C) -> A ⊕ B -> C
[ f || g ] (inl x) = f x
[ f || g ] (inr y) = g y

uncurry : {A B C : Set } -> (A -> B -> C) -> A × B -> C
uncurry f (x , y) = f x y

const : {A B : Set} -> A -> B -> A
const x y = x

foldr : {A B : Set} -> (A -> B -> B) -> B -> LIST A -> B
foldr f z = fold [ const z || uncurry f ]

plus : NAT -> NAT -> NAT
plus n m = fold [ const m || S ] n

-- Universes for overloading

open import Data.List renaming (_∷_ to _::_)

data Type : Set where
  bool : Type
  nat  : Type
  list : Type -> Type
  pair : Type -> Type -> Type

E1 : Type -> Set
E1 nat        = Nat
E1 bool       = Bool
E1 (list a)   = List (E1 a)
E1 (pair a b) = E1 a × E1 b

infix 30 _==_
_==_ : {a : Type} -> E1 a -> E1 a -> Bool

_==_ {nat} zero    zero    = true
_==_ {nat} (suc _) zero    = false
_==_ {nat} zero    (suc _) = false
_==_ {nat} (suc n) (suc m) = n == m

_==_ {bool} true  x = x
_==_ {bool} false x = not x

_==_ {list a} []        [] = true
_==_ {list a} (_ :: _)  []        = false
_==_ {list a} []        (_ :: _ ) = false
_==_ {list a} (x :: xs) (y :: ys) = x == y and xs == ys

_==_ {pair a b} (x₁ , y₁) (x₂ , y₂) = x₁ == x₂ and y₁ == y₂

example₁ : isTrue ((2 + 2) == 4)
example₁ = _               -- needed additional parenthesis

example₂ : isTrue (not ((true :: false :: []) == (true :: true :: [])))
example₂ = _               -- needed additional parenthesis

-- 3.3  Exercises

-- Exercise 3.4. An XML universe

open import Data.String renaming (_++_ to _+++_)

infixr 30 _:all:_
data All {A : Set}(P : A -> Set) : List A -> Set where
  all[]   : All P []
  _:all:_ : forall {x xs} -> P x -> All P xs -> All P (x :: xs)

Tag = String

mutual
  data Schema : Set where
    tag : Tag -> List Child -> Schema

  data Child : Set where
    text : Child
    elem : Nat -> Nat -> Schema -> Child

data BList (A : Set) : Nat -> Set where
  []   : forall {n} -> BList A n
  _::_ : forall {n} -> A -> BList A n -> BList A (suc n)

data Cons (A B : Set) : Set where
  _::_ : A -> B -> Cons A B

FList : Set -> Nat -> Nat -> Set
FList A zero    m       = BList A m
FList A (suc n) zero    = False
FList A (suc n) (suc m) = Cons A (FList A n m)

mapBList : {A B : Set}{n : Nat} -> (A -> B) -> BList A n -> BList B n
mapBList f []        = []
mapBList f (y :: y') = f y :: mapBList f y'

mapFList : {A B : Set}{n m : Nat} -> (A -> B) -> FList A n m -> FList B n m
mapFList {n = zero}           f []        = []
mapFList {n = zero}           f (y :: y') = f y :: mapBList f y'
mapFList {n = suc n} {zero}   f ()
mapFList {n = suc n} {suc n'} f (y :: y') = f y :: mapFList f y'

concatBList : {n : Nat} -> BList String n -> String
concatBList []        = ""
concatBList (y :: y') = y +++ concatBList y' 

concatFList : {n m : Nat} -> FList String n m -> String
concatFList {zero}           xs        = concatBList xs
concatFList {suc n} {zero}   ()
concatFList {suc n} {suc n'} (y :: y') = y +++ concatFList y'

mutual
  data XML : Schema -> Set where
    element : forall {kids}(t : Tag) -> All Element kids -> XML (tag t kids)

  Element : Child -> Set
  Element text         = String
  Element (elem n m s) = FList (XML s) n m

mutual
  printXML : {s : Schema} -> XML s -> String
  printXML {tag y y'} (element .y y0)
    = "<" +++ y +++ ">" +++ printChildren y0 +++ "</" +++ y +++ ">"

  printChildren : {kids : List Child} -> All Element kids -> String
  printChildren                   all[]
    = ""
  printChildren {text       :: _} (x :all: xs)
    = x +++ printChildren xs
  printChildren {elem n m s :: _} (x :all: xs)
    = concatFList (mapFList printXML x) +++ printChildren xs

myXML : XML (tag "html" ((elem (suc zero) (suc zero) (tag "head" [])) :: []))
myXML = element "html" (((element "head" all[]) :: []) :all: (all[]))

myDoc = printXML myXML