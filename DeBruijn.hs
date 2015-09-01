module Main where

-- | Model

type Label = String
type Ident = Int

data Name
    = Bound Ident
    | Free  Ident

data Expr
    = Var Name
    | Abs Label Expr | TyAbs Label Expr
    | App Expr  Expr | TyApp Expr  Expr
    
data Ty
    = TyVar  Name
    | Forall Ident Ty
    | Ty :-> Ty
    
-- | 
