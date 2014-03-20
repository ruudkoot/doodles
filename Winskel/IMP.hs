module IMP where

-- | 2.1

type Loc  = String

data Aexp
    = N Integer
    | Loc Loc
    | Aexp :+: Aexp
    | Aexp :-: Aexp
    | Aexp :*: Aexp
  deriving (Eq, Show)
    
data Bexp
    = TRUE
    | FALSE
    | Aexp :==: Aexp
    | Aexp :<=: Aexp
    | Not Bexp
    | Bexp :/\: Bexp
    | Bexp :\/: Bexp
  deriving (Eq, Show)

data Com
    = Skip
    | Loc := Aexp
    | Com ::: Com
    | If Bexp Com Com
    | While Bexp Com
  deriving (Eq, Show)

-- | 2.2

type State = Loc -> Integer

aeval :: (Aexp, State) -> Integer
aeval (N n      , _    ) = n
aeval (Loc x    , sigma) = sigma x
aeval (a0 :+: a1, sigma) = aeval (a0, sigma) + aeval (a1, sigma)
aeval (a0 :-: a1, sigma) = aeval (a0, sigma) - aeval (a1, sigma)
aeval (a0 :*: a1, sigma) = aeval (a0, sigma) * aeval (a1, sigma)

-- | 2.3

beval :: (Bexp, State) -> Bool
beval (TRUE, _) = True
beval (FALSE, _) = False
beval (a0 :==: a1, sigma) = aeval (a0, sigma) == aeval (a1, sigma)
beval (a0 :<=: a1, sigma) = aeval (a0, sigma) <= aeval (a1, sigma)
beval (Not b, sigma) = not (beval (b, sigma))
beval (b0 :/\: b1, sigma) = beval (b0, sigma) && beval (b1, sigma)
beval (b0 :\/: b1, sigma) = beval (b0, sigma) || beval (b1, sigma)

init :: State
init _ = 0

update :: State -> Integer -> Loc -> State
update sigma n loc = \loc0 -> if loc0 == loc then n else sigma loc

ceval :: (Com, State) -> State
ceval (Skip, sigma) = sigma
ceval (x := a, sigma) = let m = aeval (a, sigma) in update sigma m x
ceval (c0 ::: c1, sigma) = let sigma'' = ceval (c0, sigma) in ceval (c1, sigma'')
ceval (If b c0 c1, sigma) = ceval (if beval (b, sigma) then c0 else c1) sigma
ceval (While b c, sigma) =
    if beval (b, sigma) then
        let sigma'' = ceval (c, sigma) in ceval (While b c, sigma'')
    else
        sigma
