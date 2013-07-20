module Main where

import Prelude hiding ((&&), (||))
import Debug.Trace

p && q = case p of
           False -> False
           _     -> case q of
                      False -> False
                      _     -> True
                      
p || q = case p of
           True -> True
           _    -> case q of
                      True -> True
                      _    -> False

a p = trace ("<a " ++ show p ++ ">") p
b p = trace ("<b " ++ show p ++ ">") p

main = mapM_ print (    [ a p || b q | p <- [False, True], q <- [False, True] ]
                     ++ [ a p && b q | p <- [False, True], q <- [False, True] ])

