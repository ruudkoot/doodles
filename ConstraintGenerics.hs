{-# LANGUAGE Rank2Types #-}

module ConstraintGenerics where

newtype Name = Name String deriving (Eq, Ord, Show)

data Expr
    = Var Name
    | Con Con
    | Abs Name Ty Expr
    | App Expr Expr
    | If Expr Expr Expr
    deriving (Eq, Ord, Show)
    
data Con = Bool Bool | Int Int deriving (Eq, Ord, Show)

data Ty
    = TyVar Name
    | TyCon TyCon
    | TyFun Ty Ty
    deriving (Eq, Ord, Show)
    
data TyCon = TyBool | TyInt deriving (Eq, Ord, Show)

class Combine t where
    comb :: (forall t'. Combine t' => t' -> b) -> (b -> b -> b) -> t -> b

instance Combine Expr where
    comb f op (Var x)       = comb f op x
    comb f op (Con c)       = comb f op c
    comb f op (Abs x t e)   = comb f op x  `op` comb f op t  `op` comb f op e
    comb f op (App e1 e2)   = comb f op e1 `op` comb f op e2
    comb f op (If e0 e1 e2) = comb f op e0 `op` comb f op e1 `op` comb f op e2
    
instance Combine Name
instance Combine Con
instance Combine Ty

class IsMono t where
    isMono :: t -> Bool
    isMono _ = True

instance IsMono Name
instance IsMono Con

instance IsMono Ty where
    isMono (TyVar _)     = False
    isMono (TyCon _)     = True
    isMono (TyFun t1 t2) = isMono t1 && isMono t2

instance IsMono Expr where
    isMono = comb isMono (&&)
