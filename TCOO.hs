{-# LANGUAGE GADTs, StandaloneDeriving #-}

module Main where

-- | "Functional"
{-
-- * Original

data Expr
    = Val Int
    | Add Expr Expr
    
eval :: Expr -> Int
eval (Val n    ) = n
eval (Add e1 e2) = eval e1 + eval e2

-- * Extension (operation)

data Code = VAL Int | ADD
    deriving Show

comp :: Expr -> [Code]
comp (Val n    ) = [VAL n]
comp (Add e1 e2) = comp e1 ++ comp e2 ++ [ADD]

-- * Extension (data type)

data Expr'
    = Val' Int
    | Add' Expr' Expr'
    | Mul' Expr' Expr'

eval' :: Expr' -> Int
eval' (Val' n    ) = n
eval' (Add' e1 e2) = eval' e1 + eval' e2
eval' (Mul' e1 e2) = eval' e2 * eval' e2

-- * Extension (both)

data Code' = VAL' Int | ADD' | MUL'
    deriving Show

comp' :: Expr' -> [Code']
comp' (Val' n    ) = [VAL' n]
comp' (Add' e1 e2) = comp' e1 ++ comp' e2 ++ [ADD']
comp' (Mul' e1 e2) = comp' e1 ++ comp' e2 ++ [MUL']
-}
-- | "Object-oriented"

-- * Original

class Expr expr where eval :: expr -> Int

data Val where Val ::                             Int            -> Val
data Add where Add :: (Expr expr1, Expr expr2) => expr1 -> expr2 -> Add

instance Expr Val where eval (Val n    ) = n
instance Expr Add where eval (Add e1 e2) = eval e1 + eval e2

-- * Extension (data type)

data Mul where Mul :: (Expr expr1, Expr expr2) => expr1 -> expr2 -> Mul
instance Expr Mul where eval (Mul e1 e2) = eval e1 * eval e2

-- * Extension (operation)

class Code code

data CODE where CODE :: (Code code, Show code) => code -> CODE
deriving instance Show CODE

data VAL where VAL :: Int -> VAL deriving Show
data ADD where ADD ::        ADD deriving Show

instance Code VAL
instance Code ADD

class Expr' expr where
    eval' :: expr -> Int
    comp  :: expr -> [CODE]

data Val' where Val' ::                               Int            -> Val'
data Add' where Add' :: (Expr' expr1, Expr' expr2) => expr1 -> expr2 -> Add'

instance Expr' Val' where
    eval' (Val' n) = n
    comp  (Val' n) = [CODE $ VAL n]

instance Expr' Add' where
    eval' (Add' e1 e2) = eval' e1 + eval' e2
    comp  (Add' e1 e2) = comp e1 ++ comp e2 ++ [CODE ADD]

-- * Extension (both)

data Mul' where Mul' :: (Expr' expr1, Expr' expr2) => expr1 -> expr2 -> Mul'

data MUL where MUL :: MUL deriving Show
instance Code MUL

instance Expr' Mul' where
    eval' (Mul' e1 e2) = eval' e1 * eval' e2
    comp  (Mul' e1 e2) = comp e1 ++ comp e2 ++ [CODE MUL]
