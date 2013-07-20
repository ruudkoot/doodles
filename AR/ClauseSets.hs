{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}

module ClauseSets where

import Data.List
import Debug.Trace

-- | Literals and Atoms

data Atom literal = Pos literal
                  | Not literal
                  deriving Eq
                  
instance (Show literal) => Show (Atom literal) where
    show (Pos l) =       show l
    show (Not l) = '~' : show l

instance Show (Atom Char) where
    show (Pos l) =       [l]
    show (Not l) = '~' : [l]
                  
lit :: Atom literal -> literal
lit (Pos l) = l
lit (Not l) = l
                  
neg :: Atom literal -> Atom literal
neg (Pos l) = Not l
neg (Not l) = Pos l

-- | Clause sets

type Clause    literal = [Atom literal]
type ClauseSet literal = [Clause literal]

-- | DPLL and rules

                
dpll :: (Eq literal, Show literal) => ClauseSet literal -> Bool
dpll c = let c' = fixPoint' [oneLiteralRule, tautologyRule] c
         in if null c' then True else splittingRule c'

fixPoint :: Eq a => (a -> a) -> a -> a
fixPoint f = takeFixPoint . iterate f

fixPoint' :: Eq a => [a -> a] -> a -> a
fixPoint' fs = takeFixPoint . iterate (fixPoint'' fs)
    where -- fixPoint'' :: [a -> a] -> a -> a
          fixPoint'' []     = id --fixPoint'' fs
          fixPoint'' (f:fs) = fixPoint'' fs . fixPoint f

takeFixPoint :: Eq a => [a] -> a
takeFixPoint (x1:xs@(x2:_)) | x1 == x2  = x1
                            | otherwise = takeFixPoint xs

splittingRule :: (Eq literal, Show literal) => ClauseSet literal -> Bool
splittingRule c = let p  = selectLiteral c
                      c1 = [Pos p] : c
                      c2 = [Not p] : c
                  in dpll c1 || dpll c2
                  
selectLiteral :: ClauseSet literal -> literal
selectLiteral []         = error "empty clause set"
selectLiteral ([]:cs)    = selectLiteral cs
selectLiteral ((a:as):_) = lit a

oneLiteralRule :: (Eq literal, Show literal) => ClauseSet literal -> ClauseSet literal
oneLiteralRule c = case findSingleAtomClause c of
                     Just a  -> oneLiteralRule' a c
                     Nothing -> c
                     
findSingleAtomClause :: ClauseSet literal -> Maybe (Atom literal)
findSingleAtomClause cs = let singleAtomClauses = filter (\x -> length x == 1) cs
                          in if null singleAtomClauses
                             then Nothing
                             else Just (head (head singleAtomClauses))

oneLiteralRule' :: (Eq literal, Show literal) => Atom literal -> ClauseSet literal -> ClauseSet literal
oneLiteralRule' a []     = []
oneLiteralRule' a (c:cs) | a `elem` c = oneLiteralRule' a cs
                         | otherwise  = (c \\ [neg a]) : oneLiteralRule' a cs

tautologyRule :: (Eq literal, Show literal) => ClauseSet literal -> ClauseSet literal
tautologyRule []     = []
tautologyRule (c:cs) = let ls = literals c -- this can't be right
                        in if or (map (\l -> l `elem` c && neg l `elem` c) ls)
                           then tautologyRule cs
                           else c : tautologyRule cs

literals :: Clause literals -> [Atom literals]
literals []           = []
literals (a : as) = a : literals as
--literals (a : as) = a : literals as

-- | Tests

ex1 = [[Pos 't'], [Not 't', Not 'r'], [Pos 'p', Not 'r', Pos 's', Not 't'], [Not 'p', Pos 'q', Pos 'r'], [Not 's', Pos 'u', Not 'u'], [Pos 'p', Not 'q', Not 't'], [Pos 'p', Pos 't']]
