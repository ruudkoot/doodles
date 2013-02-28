{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE TupleSections                                        #-}

module ConstraintBasedAnalysis where

import Data.List.Util (worklist)
import Data.Map (Map, (!), adjust, insert)
import qualified Data.Map as Map
import Data.Set (Set, empty, singleton, union, member, fromList, toList)
import qualified Data.Set as Set
import Data.Set.Util (unionMap)

toMap = Map.fromList

-- | Expressions

type Name = String
type Lab  = Integer

type Expr = (Term, Lab)

data Term
    = Con Int
    | Var Name
    | Fn  Name Expr
    | Fun Name Name Expr
    | App Expr Expr
    | If  Expr Expr Expr
    | Let Name Expr Expr
    | Op  Expr Op   Expr
    deriving (Eq, Ord, Show)
    
data Op
    = ADD
    deriving (Eq, Ord, Show)

-- | Constraints

data Constr
    = LHS :<: RHS
    deriving (Eq, Ord, Show)

type LHS = S LH
type RHS = S RH

data H = LH | RH
    deriving (Eq, Ord, Show)
    
data S :: H -> * where
    R    :: Name                 -> S h
    C    :: Lab                  -> S h
    FN   :: Name -> Expr         -> LHS
    FUN  :: Name -> Name -> Expr -> LHS
    IMPL :: Term -> RHS  -> LHS  -> LHS

deriving instance Eq   (S a)
deriving instance Ord  (S a)
deriving instance Show (S a)

-- | Constraint Generation

c' :: Expr -> Set Constr
c' e = c e
    where
      c :: Expr -> Set Constr
      c (Con _, _)
        = empty
      c (Var x, l)
        = singleton (R x :<: C l)
      c (Fn x e0, l)
        = singleton (FN x e0 :<: C l)
      c (Fun f x e0, l)
        = singleton (FUN f x e0 :<: C l)
      c (App (t1, l1) (t2, l2), l)
        = c (t1, l1) `union` c (t2, l2) `union` unionMap q terms'
            where q t@(Fn    x (t0, l0))
                    = fromList [ IMPL t (C l1) (C l2) :<: R x
                               , IMPL t (C l1) (C l0) :<: C l ]
                  q t@(Fun f x (t0, l0))
                    = fromList [ IMPL t (C l1) (C l2) :<: R x
                               , IMPL t (C l1) (C l0) :<: C l ]
                  q _
                    = empty
      c (If (t0, l0) (t1, l1) (t2, l2), l)
        = c (t0, l0) `union` c (t1, l1) `union` c (t2, l2)
            `union` fromList [ C l1 :<: C l, C l2 :<: C l ]
      c (Let x (t1, l1) (t2, l2), l)
        = c (t1, l1) `union` c (t2, l2)
            `union` fromList [ C l1 :<: R x, C l2 :<: C l ]
      c (Op (t1, l1) op (t2, l2), l)
        = c (t1, l1) `union` c (t2, l2)
        
      terms' :: Set Term
      terms' = terms e

      terms :: Expr -> Set Term
      terms (Con c, l)
        = singleton (Con c)
      terms (Var x, l)    
        = singleton (Var x)
      terms (Fn x e0, l)
        = singleton (Fn x e0)
            `union` terms e0
      terms (Fun f x e0, l)
        = singleton (Fun f x e0)
            `union` terms e0
      terms (App e1 e2, l)
        = singleton (App e1 e2)
            `union` terms e1 `union` terms e2
      terms (If e1 e2 e3, l)
        = singleton (If e1 e2 e3)
            `union` terms e1 `union` terms e2 `union` terms e3
      terms (Let x e1 e2, l)
        = singleton (Let x e1 e2)
            `union` terms e1 `union` terms e2
      terms (Op e1 op e2, l)
        = singleton (Op e1 op e2)
            `union` terms e1 `union` terms e2
            
-- | Constraint Solving

type Cache     = Map Lab  (Set Term)
type Env       = Map Name (Set Term)

type Val       = LHS

type Node      = RHS
type Worklist  = [Node]
type DataArray = Map Node (Set Val)
type EdgeArray = Map Node [Constr]

solve :: [Node] -> Set Constr -> (Cache, Env)
solve nodes constraints
    = -- FIXME: State monad...
      let (w , d , e ) = initialize
          (w', d', e') = buildGraph w d e
          ()           = iteration
          ()           = recordSolution
       in undefined
    where
        initialize :: (Worklist, DataArray, EdgeArray)
        initialize
            = ([], toMap (map (, empty) nodes), toMap (map (, []) nodes))

        buildGraph :: Worklist -> DataArray -> EdgeArray -> (Worklist, DataArray, EdgeArray)
        buildGraph w d e
            = Set.foldr f (w, d, e) constraints
                where f :: Constr -> (Worklist, DataArray, EdgeArray) -> (Worklist, DataArray, EdgeArray)
                      f    (t@(FN  _   _) :<: p ) (d, e)
                        = add p t
                      f    (t@(FUN _ _ _) :<: p ) (d, e)
                        = add p t
                      f cc@(p1            :<: p2) (d, e)
                        = (w, d,                  adjust (cc:) p1 e)
                      f cc@(IMPL t p p1   :<: p2) (d, e)
                        = (w, d, adjust (cc:) p $ adjust (cc:) p1 e)

                      add :: RHS -> LHS -> (Worklist, DataArray, EdgeArray)
                      add q u
                        | u `member` (d ! q) = ((                        d, e), [ ])
                        | otherwise          = ((adjust (Set.insert u) q d, e), [q])

        iteration :: ()
        iteration = undefined
        
        recordSolution :: ()
        recordSolution = undefined

-- | Examples

ex320 = (App (Fn "x" (Var "x", 1), 2) (Fn "y" (Var "y", 3), 4), 5)

cfa e = solve (nodes e) $ c' e

nodes = undefined
