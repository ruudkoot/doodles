module Substructural where

import Data.List

-- | Syntax

type Name = String

data Qual
    = Lin
    | Un
    deriving (Eq, Ord, Show)

data Tm
    = Var Name
    | Bool Qual Bool
    | If Tm Tm Tm
    | Pair Qual Tm Tm
    | Split Tm Name Name Tm
    | Abs Qual Name Ty Tm
    | App Tm Tm
    deriving (Eq, Ord, Show)
    
data PreTy
    = TyBool
    | TyPair Ty Ty
    | TyFun Ty Ty
    deriving (Eq, Ord, Show)

data Ty = Ty Qual PreTy
    deriving (Eq, Ord, Show)

type Ctx = [(Name,Ty)]

-- | Algorithmic Typing

typeCheck :: Ctx -> Tm -> (Ty, Ctx)
typeCheck env (Var x)
    | Just ty@(Ty Un  p) <- lookup x env = (ty,                env)
    | Just ty@(Ty Lin p) <- lookup x env = (ty, delete (x, ty) env)
    | otherwise                          = error "scope"
typeCheck env (
