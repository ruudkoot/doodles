module Main where

allb :: ([Bool] -> Bool) -> Bool
allb f = f (counterexample f)

counterexample :: ([Bool] -> Bool) -> [Bool]
counterexample f = if allb f_t then
                        False : counterexample f_f
                   else
                        True  : counterexample f_t
    where f_t = \s -> f (True  : s)
          f_f = \s -> f (False : s)
