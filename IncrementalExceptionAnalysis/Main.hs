{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Main where

import Control.Monad
import Control.Monad.State

import qualified Data.List as L
import qualified Data.Map  as M
import           Data.Maybe
import qualified Data.Set  as S

import Fresh
import Parsing
import Printing

import Syntax
import Analysis
import TypeInfer
import CallByValue
-- import CallByName

-- | Examples

main
    = do putStrLn preamble
         example "Example 1" ex1
         example "Example 2" ex2
         example "Example 3" ex3
         putStrLn postamble
          
example name ex
    = do putStrLn ("\\paragraph{" ++ name ++ "}")
         putStrLn "\\begin{gather}"
         putStrLn (latex ex ++ newline)
         let ((t, subst), _) = runState (infer M.empty ex) freshIdents
         putStrLn (latex t ++ newline)
         let ((t, eff, subst, k), _) = runState (analyzeCBV M.empty ex) freshIdents
         putStrLn ("\\left(" ++ latex t ++ ", " ++ latex eff ++ ", " ++ latex subst ++ ", " ++ latex k ++ "\\right)" ++ newline)
         let kbar = bar k
         putStrLn (latex kbar ++ newline)
         let Eff eff' = bar k $$@# eff
         let sol = S.filter f eff'
                    where f EffCrash = True
                          f _        = False
         putStrLn ("\\left(" ++ latex t ++ ", " ++ latex sol ++ "\\right)" ++ newline)
--       let ((t, eff, subst, k), _) = runState (analyzeCBN M.empty ex) freshIdents
--       putStrLn ("(" ++ latex t ++ ", " ++ latex eff ++ ")" ++ newline)
         putStrLn (latex (cbv ex) ++ newline)
         putStrLn (latex (cbn ex))
         putStrLn "\\end{gather}"

ex1 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Int 3))) (Con (Bool False)))
ex2 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (App (App (Var "const") (Con (Bool True))) Crash)
ex3 = Let "const" (Abs "k" (Abs "x" (Var "k"))) (Var "const")
ex4 = Let "id" (Abs "x" (Var "x")) (App (Var "id") (Var "id")) -- needs let-polymorphism
