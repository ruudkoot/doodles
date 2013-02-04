{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Main where

import qualified Data.Dequeue as Deq
import Data.List (intersperse)

-- | 2

-- * 2.1 Basic combinators

type Indent = Int
type Width  = Int
type Layout = String

class Doc d where
    text :: String -> d
    line :: d
    group :: d -> d
    (<>) :: d -> d -> d
    nest :: Indent -> d -> d
    pretty :: Width -> d -> Layout
    nil :: d
    nil = text ""
    
prettyIO :: Doc d => Width -> d -> IO ()
prettyIO w d = putStrLn (pretty w d)

toDoc :: Doc d => [Int] -> d
toDoc = (text "[" <>)
        . foldr (<>) (text "]")
        . intersperse (group (text "," <> line))
        . map (text . show)
        
-- * 2.2 Straightforward implementations

type Position   = Int
type Remaining  = Int
type Horizontal = Bool
type Spec       = (Indent, Width) -> Horizontal -> Position -> Remaining
                        -> (Position, Remaining, Layout)

instance Doc Spec where
    text t     iw h p r = (p + l, r - l,  t) where l = length t
    line       iw h p r = (p + 1,    rl, ll) where (rl, ll) = newLine iw h r
    (dl <> dr) iw h p r = (pr, rr, ll ++ lr) where (pl, rl, ll) = dl iw h p  r
                                                   (pr, rr, lr) = dr iw h pl rl
    group   d  iw h p r = let v@(pd, _, _) = d iw (pd - p <= r) p r in v
    nest  j d  (i, w)   = d (i + j, w)
    pretty w d          = let (_, _, l) = d (0, w) False 0 w in l
    
newLine (i, w) True  r = (r - 1, [' ']                 )
newLine (i, w) False r = (w - i, '\n' : replicate i ' ')

type Norm d = d -> (d, d)

instance Doc d => Doc (Norm d) where
    text t     tt = (text t <> tt, nil )
    line       tt = (nil, line <> tt)
    (dl <> dr) tt = let (tdl, sdl) = dl tdr
                        (tdr, sdr) = dr tt
                     in (tdl, sdl <> sdr)
    group   d  tt = mapsnd group    (d tt)
    nest  j d  tt = mapsnd (nest j) (d tt)
    pretty w d    = let (td, sd) = d nil in pretty w (td <> sd)
    nil        tt = (tt, nil)

mapsnd f (x, y) = (x, f y)

-- | 3  Solutions

type Horizontals = [Horizontal]
type P           = Horizontals
type C           = Horizontals
type Dq          = Deq.BankersDequeue (Position, Horizontals)
type State       = (Position, Dq, C, Remaining)
type Lazy        = (Indent, Width) -> State -> (State, Layout, P)

enter :: Position -> Dq -> Dq
enter mep q = q `Deq.pushFront` (mep, [])

leave :: Position -> Dq -> (Dq, P)
leave p q = case Deq.length q of
                0 -> (Deq.empty, [])
                1 -> let (Just (mep, hs), _) = Deq.popFront q
                      in (Deq.empty, True : hs)
                _ -> undefined
