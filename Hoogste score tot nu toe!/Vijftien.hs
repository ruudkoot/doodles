{-# LANGUAGE TupleSections  #-}
{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Control.Monad

import Data.Array
import Data.List
import Data.Maybe
import Data.Tree

(?>) :: MonadPlus m => Bool -> a -> m a
p ?> x | p         = return x
       | otherwise = mzero

infix 0 ?>

data Field = F1  | F2  | F3  | F4
           | F5  | F6  | F7  | F8
           | F9  | F10 | F11 | F12
           | F13 | F14 | F15 | H
	deriving (Eq, Ord, Enum)

instance Show Field where
	show F1 = "1"
	show F2 = "2"
	show F3 = "3"
	show F4 = "4"
	show F5 = "5"
	show F6 = "6"
	show F7 = "7"
	show F8 = "8"
	show F9 = "9"
	show F10 = "A"
	show F11 = "B"
	show F12 = "C"
	show F13 = "D"
	show F14 = "E"
	show F15 = "F"
	show H = "#"

type Coord = (Int, Int)

type Board = Array Coord Field

data State = State { board :: Board, hole :: Coord }
	deriving Eq
	
instance Show State where
	show (State {board}) = concatMap show (elems board)

initial :: State
initial = State { board = listArray ((1,1),(4,4)) [F1 .. H]
                , hole  = (4, 4)                            }

moves :: State -> [State]
moves st@(State {board, hole = (hx, hy)}) = catMaybes [up, down, left, right] where
	up    = hy > 1 ?> move (hx,hy-1)
	down  = hy < 4 ?> move (hx,hy+1)
	left  = hx > 1 ?> move (hx-1,hy)
	right = hx < 4 ?> move (hx+1,hy)
	move (hx',hy') =
		State { board = board // [((hx,hy), board ! (hx',hy')), ((hx',hy'),H)]
		      , hole  = (hx',hy')                                              }

gameTree st = st `Node` map gameTree (moves st)

all' :: (a -> Bool) -> Tree a -> Bool
all' p (Node a as) = p a && all (all' p) as

bfs :: (a -> Bool) -> Tree a -> ([a], [a])
bfs p t@(Node a as) = undefined


solved :: State -> Bool
solved st = st == initial

main = print $ flatten (gameTree initial)
