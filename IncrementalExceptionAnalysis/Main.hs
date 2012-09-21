module Main where

import Control.Monad
import Control.Monad.State

import qualified Data.Map as M
import qualified Data.Set as S

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
         example "Example 1" ex1
         example "Example 2" ex2
         example "Example 3" ex3
         putStrLn postamble
          
example name ex
    = do putStrLn $ "\\paragraph{" ++ name ++ "}"
         putStrLn $ "\\begin{gather}"
         -- Syntax tree
         putStrLn $ latex ex ++ newline
         -- Type inference
         let ((t, subst), _) = runState (TI.infer M.empty ex) freshIdents
         putStrLn $ latex t ++ newline
         -- Call-by-value
         let ((t, eff, subst, k), _) = runState (CBV.infer M.empty ex) freshIdents
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
         -- Call-by-name
         let ((t, eff, subst, k), _) = runState (CBN.infer M.empty ex) freshIdents
         putStrLn $ "\\left(" ++ latex t ++ ", " ++ latex eff ++ ", "
                              ++ latex subst ++ ", " ++ latex k
                              ++ "\\right)" ++ newline
         let kbar = CBN.bar k
         putStrLn $ latex kbar ++ newline
         let Eff eff' = kbar CBN.$*@ eff
         let sol = S.filter f eff'
                    where f EffCrash = True
                          f _        = False
   --    putStrLn $ "\\left(" ++ latex t ++ ", " ++ latex sol ++ "\\right)" ++ newline
         -- Evaluation
         putStrLn $ latex (cbv ex) ++ newline
         putStrLn $ latex (cbn ex)
         putStrLn $ "\\end{gather}"

ex1 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Int 3))) (Con (Bool False)))
ex2 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Bool True))) Crash)
ex3 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (Var "const")
ex4 = Let "id" (Abs "x" (Var "x")) (App (Var "id") (Var "id")) -- needs let-polymorphism
