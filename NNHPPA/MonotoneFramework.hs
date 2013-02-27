{-# LANGUAGE TupleSections #-}

module MonotoneFramework where

import           Prelude         hiding ((!!), init)
import qualified Data.Map   as M
import           Data.Map        ((!))
import           Data.Set   as S
import           Data.Tuple

-- | Syntax

type Name = String
type Lab  = Int

data OpA
    = ADD
    | MUL
    deriving (Eq, Ord, Show)
    
data OpB
    = AND
    | OR
    deriving (Eq, Ord, Show)

data OpR
    = EQ
    deriving (Eq, Ord, Show)

data AExp
    = Var Name
    | ConA Int
    | OpA AExp OpA AExp
    deriving (Eq, Ord, Show)
    
data BExp
    = ConB Bool
    | Not BExp
    | OpB BExp OpB BExp
    | OpR BExp OpR BExp
    deriving (Eq, Ord, Show)    
    
data Stmt
    = Assign Name AExp Lab
    | Skip Lab
    | Seq Stmt Stmt
    | If BExp Lab Stmt Stmt
    | While BExp Lab Stmt
    deriving (Eq, Ord, Show)

-- | Data flow

-- * Initial and final labels

init :: Stmt -> Lab
init (Assign _ _ l) = l
init (Skip l)       = l
init (Seq s1 s2)    = init s1
init (If b l s1 s2) = l
init (While b l s)  = l

final :: Stmt -> Set Lab
final (Assign _ _ l) = singleton l
final (Skip l)       = singleton l
final (Seq s1 s2)    = final s2
final (If b l s1 s2) = final s1 `union` final s2
final (While b l s)  = singleton l

-- * Blocks

data Blocks
    = Assign' Name AExp Lab
    | Skip' Lab
    | Test BExp Lab
    deriving (Eq, Ord, Show)

blocks :: Stmt -> Set Blocks
blocks (Assign x a l) = singleton (Assign' x a l)
blocks (Skip l)       = singleton (Skip' l)
blocks (Seq s1 s2)    = blocks s1 `union` blocks s2
blocks (If b l s1 s2) = singleton (Test b l) `union` blocks s1 `union` blocks s2
blocks (While b l s)  = singleton (Test b l) `union` blocks s

block :: Stmt -> Lab -> Blocks
block 

labels :: Stmt -> Set Lab
labels s = S.map prjL (blocks s)
    where prjL :: Blocks -> Lab
          prjL (Assign' _ _ l) = l
          prjL (Skip'       l) = l
          prjL (Test _      l) = l

-- * Flows and reverse flows

type Flow = Set (Lab, Lab)

flow :: Stmt -> Flow
flow (Assign _ _ _)
    = empty
flow (Skip _)
    = empty
flow (Seq s1 s2)
    = flow s1 `union` flow s2 `union` S.map (, init s1) (final s1)
flow (If b l s1 s2)
    = flow s1 `union` flow s2 `union` fromList [(l, init s1), (l, init s2)]
flow (While b l s)
    = flow s `union` singleton (l, init s) `union` S.map (, l) (final s)

flowR = S.map swap . flow

-- | Monotone Framework

type CompleteLattice l = (l -> l -> Bool, l -> l -> l, l, l)

-- | Solver

-- * Maximal Fixed Point

mfp :: CompleteLattice l -> (M.Map Lab (l -> l)) -> Flow -> Set Lab -> (M.Map Lab l, M.Map Lab l)
mfp lattice@((<<), join, bottomL, topL) transferFunctions flow extremalLabels
    = let worklist
            = flow
          analysis
            = S.foldr (\l -> M.insert l topL)
                      (S.foldr (\(l, l') -> M.insert l bottomL . M.insert l' bottomL)
                               M.empty
                               flow                                                  )
                      extremalLabels
          (worklist', analysis')
            = whileNotNil (worklist, analysis) (\(worklist, analysis) -> 
                let Just ((l, l'), worklist') = minView worklist
                    fl = transferFunctions ! l
                 in if fl (analysis ! l) << (analysis ! l')
                    then (worklist', analysis)
                    else let analysis'
                                = M.adjust (join (fl (analysis ! l))) l' analysis
                             worklist''
                                = worklist' `union` S.filter (\(m, _) -> m == l') flow
                          in (worklist'', analysis')
              )
       in forallL flow extremalLabels (\l (mfpO, mfpC) ->
            ( M.insert l                          (analysis' ! l)  mfpO
            , M.insert l ((transferFunctions ! l) (analysis' ! l)) mfpC ) )
            (M.empty, M.empty)

forallL :: Flow -> Set Lab -> (Lab -> r -> r) -> r -> r
forallL f e g i
    = S.foldr (\l -> g l) (S.foldr (\(l, l') -> g l . g l') i f) e

whileNotNil :: (Set a, b) -> ((Set a, b) -> (Set a, b)) -> (Set a, b)
whileNotNil (w, a) f
    = if S.null w
      then (w, a)
      else whileNotNil (f (w, a)) f
