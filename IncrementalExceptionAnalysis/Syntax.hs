module Syntax where

import qualified Data.Map   as M
import           Data.Maybe

import Fresh
import Printing

-- | Syntax

data Expr
    = Var Ident
    | Con Con
    | Abs Ident Expr
    | App Expr Expr
    | If Expr Expr Expr
    | Let Ident Expr Expr
    | Crash
    | Close Expr Env
    deriving (Eq, Ord, Show)

data Con
    = Bool Bool
    | Int  Int
    deriving (Eq, Ord, Show)

instance LaTeX Expr where
    latex (Var x)            = x
    latex (Con (Bool True )) = "\\mathbf{True}"    
    latex (Con (Bool False)) = "\\mathbf{False}"
    latex (Con (Int n     )) = show n
    latex (Abs x e         ) = "\\left(\\lambda " ++ x ++ ".\\ " ++ latex e ++ "\\right)"
    latex (App e1 e2       ) = latex e1 ++ "\\ " ++ latex e2
    latex (If e0 e1 e2     ) = "\\mathbf{if}\\ " ++ latex e0
                               ++ "\\ \\mathbf{then}\\ " ++ latex e1
                               ++ "\\ \\mathbf{else}\\ " ++ latex e2
    latex (Let x e1 e2     ) = "\\mathbf{let}\\ " ++ x
                               ++ "\\ \\mathbf{=}\\ " ++ latex e1
                               ++ "\\ \\mathbf{in}\\ " ++ latex e2
    latex (Crash           ) = "\\lightning"
    latex (Close e env     ) = "\\mathbf{close}\\ " ++ latex e
                               ++ "\\ \\mathbf{in}\\ " ++ latex env
                               
-- | Dynamics

type Env = M.Map Ident Expr

-- * Call-by-value

cbv :: Expr -> Expr
cbv = cbv' M.empty

cbv' :: Env -> Expr -> Expr
cbv' env (Var x)
    = fromJust (M.lookup x env)
cbv' env (Con c)
    = Con c
cbv' env (Abs x e)
    = Close (Abs x e) env
cbv' env (App e1 e2)
    = case cbv' env e2 of
        Crash -> Crash
        v2    -> case cbv' env e1 of
                    Crash -> Crash
                    Close (Abs x e1') env' -> cbv' (M.insert x v2 env') e1'
cbv' env (If e0 e1 e2)
    = case cbv' env e0 of
        Con (Bool True ) -> cbv' env e1
        Con (Bool False) -> cbv' env e2
cbv' env (Let x e1 e2)
    = case cbv' env e1 of
        Crash -> Crash
        v1    -> cbv' (M.insert x v1 env) e2
cbv' env Crash
    = Crash
    
-- Call-by-name
-- FIXME: this Close and no Bind is weird...
-- FIXME: if-then-else etc.
    
cbn :: Expr -> Expr
cbn = cbn' M.empty

cbn' :: Env -> Expr -> Expr
cbn' env (Var x)
    = fromJust (M.lookup x env)
cbn' env (Con c)
    = Close (Con c) env
cbn' env (Abs x e)
    = Close (Abs x e) env
cbn' env (App e1 e2)
    = case cbn' env e1 of
        Crash                  -> Crash
        Close (Abs x e1') env' -> cbn' (M.insert x e2 env') e1'
        x                      -> error $ show x
cbn' env (Let x e1 e2)
    = cbn' (M.insert x (Close e1 env) env) e2
cbn' env Crash
    = Crash
