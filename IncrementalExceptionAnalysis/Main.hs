module Main where

import Control.Monad
import Control.Monad.State

import qualified Data.Map         as M
import qualified Data.Set         as S
import qualified Data.Tree        as T
import qualified Data.Tree.Zipper as Z

import Fresh
import Parsing
import Printing

import Syntax
import Analysis
import qualified TypeInfer   as TI
import qualified CallByValue as CBV
import qualified CallByName  as CBN

-- | Examples

main
    = do putStrLn preamble
         example "Example 1"  ex1
         example "Example 2"  ex2
         example "Example 3"  ex3
         example "Example 4"  ex4
         example "Example 5"  ex5
         example "Example 6"  ex6
         example "Example 7"  ex7
         example "Example 8"  ex8
         example "Example 9"  ex9
         example "Example 10" ex10
         putStrLn postamble
          
example name ex
    = do putStrLn $ "\\paragraph{" ++ name ++ "}"
         putStrLn $ "\\begin{gather}"
         -- Syntax tree
         putStrLn $ latex ex ++ newline
         -- Type inference
         let ((t, subst), _) = runState (TI.infer M.empty ex) initialState
         putStrLn $ latex t ++ newline
         -- Call-by-value
         let ((t, eff, subst, k), _) = runState (CBV.infer M.empty ex) initialState
         putStrLn $ "\\left(" ++ latex t ++ ", " ++ latex eff ++ ", "
                              ++ latex subst ++ ", " ++ latex k
                              ++ "\\right)" ++ newline
         let kbar = CBV.bar k
         putStrLn $ latex kbar ++ newline
         let Eff eff' = kbar CBV.$*@ eff
         let sol = S.filter f eff'
                    where f EffCrash = True
                          f _        = False
         putStrLn $ "\\left(" ++ latex t ++ ", " ++ latex sol ++ "\\right)" ++ newline  
         putStrLn $ latex (cbv ex) ++ newline
         -- Call-by-name
         let ((t, eff, subst, k), (_, tr)) = runState (CBN.infer M.empty ex) initialState
         putStrLn $ "\\left(" ++ latex t ++ ", " ++ latex eff ++ ", "
                              ++ latex subst ++ ", " ++ latex k
                              ++ "\\right)" ++ newline
         let kbar = CBN.bar k
         putStrLn $ latex kbar ++ newline
         let Eff eff' = kbar CBN.$*@ eff
         let sol = S.filter f eff'
                    where f EffCrash = True
                          f _        = False
         putStrLn $ "\\left(" ++ latex t ++ ", " ++ latex sol ++ "\\right)" ++ newline
         putStrLn $ latex (kbar CBN.$*@ subst CBN.$@ Z.toTree tr) ++ newline
         putStrLn $ latex (cbn ex)
         putStrLn $ "\\end{gather}"

ex1 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Int 3))) (Con (Bool False)))
ex2 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Bool True))) Crash)
ex3 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (Var "const")
ex4 = (App Crash Crash)
ex5 = (App Crash (Con (Bool True)))
ex6 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (Var "const") Crash)
ex7 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") Crash) (Con (Bool True)))
ex8 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Bool True))) Crash)
ex9 = Let "suspendedcrash" (Abs "x" Crash) (Var "suspendedcrash")
ex10 = Let "suspendedcrash" (Abs "x" Crash) (App (Var "suspendedcrash") (Con (Bool True)))
ex11 = If Crash (Con (Bool True)) (Con (Bool False))
-- ex12 = If (Con (True)) (Con (Bool False)) Crash
exP = Let "id" (Abs "x" (Var "x")) (App (Var "id") (Var "id")) -- needs let-polymorphism

-- | More pretty-printing

instance CBN.Substitute a => CBN.Substitute (T.Tree a) where
    subst $@ (T.Node x cs) = T.Node (subst CBN.$@ x) (map (subst CBN.$@) cs)
    
instance CBN.Substitute' a => CBN.Substitute' (T.Tree a) where
    subst $*@ (T.Node x cs) = T.Node (subst CBN.$*@ x) (map (subst CBN.$*@) cs)
