{-# LANGUAGE RankNTypes #-}

module ASG4DSL where

-- | 2.  Sharing in EDSLs

data Expr a
    = One
    | Add (Expr a) (Expr a)
    | Var a
    | Let (Expr a) (a -> Expr a)
    
type ClosedExpr = forall a. Expr a

one :: Expr a
one = One

(#) :: Expr a -> Expr a -> Expr a
(#) = Add

let_ :: Expr a -> (Expr a -> Expr a) -> Expr a
let_ e1 e2 = Let e1 (\x -> e2 (Var x))

treeI :: Int -> Expr a
treeI 0 = one
treeI n = let shared = treeI (n - 1) in shared # shared

treeE :: Int -> Expr a
treeE 0 = one
treeE n = let_ (treeE (n - 1)) (\shared -> shared # shared)

eval :: Expr Int -> Int
eval One         = 1
eval (Add e1 e2) = eval e1 + eval e2
eval (Var n)     = n
eval (Let e1 e2) = eval (e2 (eval e1))

text :: ClosedExpr -> String
text e = go e 0
    where
        go :: Expr String -> Int -> String
        go One _ = "1"
        go (Add e1 e2) c = "(" ++ go e1 c ++ " + " ++ go e2 c ++ ")"
        go (Var x) _ = x
        go (Let e1 e2) c = "(let " ++ v ++ " = " ++ go e1 (c + 1)
                           ++ " in " ++ go (e2 v) (c + 1) ++ ")"
            where v = "v" ++ show c

inline :: Expr (Expr a) -> Expr a
inline One         = One
inline (Add e1 e2) = Add (inline e1) (inline e2)
inline (Var x)     = x
inline (Let e1 e2) = inline (e2 (inline e1))
