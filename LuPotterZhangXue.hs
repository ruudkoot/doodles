{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Main where

import Control.Monad
import Control.Monad.State

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S
import qualified Data.Tree as T

-- | Main

main =  do let expr = Fn "x" (Var "x")
           let init = (freshIdents, ())
           let (res@(t, de, subst, k), (_, ())) = runState (infer M.empty expr) init
           putStrLn $ "Type  : " ++ show t
           putStrLn $ "DetEff: " ++ show de
           putStrLn $ "Subst : " ++ show subst
           putStrLn $ "Constr: " ++ show k

-- | Syntax

type Name   = String

type Ident  = Name
type Label  = Name
type Region = S.Set Label

data Expr
    = Int Int
    | Fn Ident Expr
    | Var Ident
    | App Expr Expr
    | Ref Label Expr
    | Deref Expr
    | Expr := Expr
    | Fork Expr
    | Det Expr
    deriving (Eq, Ord, Show)
    
_let x e1 e2 = App (Fn x e2) e1
_seq   e1 e2 = _let "_" e1 e2

-- | Static semantics

data Ty
    = TyVar Name
    | TyInt
    | TyFun Ty DetEff Ty
    | TyRef Region Ty
    deriving (Eq, Ord, Show)

data Eff'
    = EffVar Name
    | EffDeref Region
    | EffAssign Region
    | EffFork Eff
    | EffDet Eff
    deriving (Eq, Ord, Show)
    
data Eff
    = EffUnif Name
    | Eff (S.Set Eff')
    deriving (Eq, Ord, Show)

data Lvl' = Weak | Non deriving (Eq, Ord, Show)

data Lvl
    = LvlVar Name
    | Lvl Lvl'
    deriving (Eq, Ord, Show)

type DetEff = (Eff, Lvl)

type TyEnv = M.Map Ident Ty

-- * Constraints

data Constr'
    = Eq DetEff DetEff
    | Seq DetEff DetEff DetEff
    deriving (Eq, Ord, Show)
    
type Constr = S.Set Constr'


-- | Unification

unify :: Ty -> Ty -> Subst
unify TyInt TyInt
    = idSubst
unify (TyVar a) (TyVar a')
    = Subst (M.singleton a (TyVar a')) M.empty
unify (TyVar a) t
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = Subst (M.singleton a t) M.empty
unify t (TyVar a)
    | a `S.member` ftv t = error "occurs check"
    | otherwise          = Subst (M.singleton a t) M.empty
unify (TyFun t1 de t2) (TyFun t1' de' t2')
    = let s1 = unify' (            de) (            de')
          s2 = unify  (      s1 $@ t1) (      s1 $@ t1')
          s3 = unify  (s2 $@ s1 $@ t2) (s2 $@ s1 $@ t2')
       in s3 $. s2 $. s1
unify _ _
    = error "constructor clash"

unify' :: DetEff -> DetEff -> Subst
unify' (EffUnif e1, LvlVar d1) (EffUnif e2, LvlVar d2)
    = Subst M.empty (M.fromList [(e1, e2), (d1, d2)])
unify' _ _
    = error "not a simple type"

-- * Inference

infer :: TyEnv -> Expr -> State ([Name], ()) (Ty, DetEff, Subst, Constr)
infer env (Int c)
    = do de <- fresh
         return ( TyInt, de, idSubst
                , S.fromList [Eq (Eff S.empty, Lvl Weak) de] )
infer env (Var x)
    | Just t <- M.lookup x env
        = do de <- fresh
             return ( t, de, idSubst
                    , S.fromList [Eq (Eff S.empty, Lvl Weak) de] )
    | otherwise = error "variable not in scope"
infer env (Fn x e)
    = do t2 <- fresh
         (t1, de1, subst1, k1) <- infer (M.insert x t2 env) e
         de <- fresh
         return ( TyFun (subst1 $@ t2) de1 t1, de, subst1
                , S.fromList [Eq (Eff S.empty, Lvl Weak) de] `S.union` k1)
infer env (App e1 e2)
    = do (t1', de1, subst1, k1) <- infer env e1
         (t2 , de2, subst2, k2) <- infer (subst1 $@ env) e2
         t1 <- fresh
         e3 <- fresh
         d3 <- fresh
         let subst3 = unify (subst2 $@ t1') (TyFun t2 (e3, d3) t1)
         de' <- fresh
         de  <- fresh
         return ( subst3 $@ t1, (subst3 $@ e3, subst3 $@ d3)
                , subst3 $. subst2 $. subst1
                , S.fromList [ Seq (subst3 $@ subst2 $@ de1) (subst3 $@ de2) de'
                             , Seq de' (subst3 $@ (e3, d3)) de                   ]
                  `S.union` (subst3 $@ subst2 $@ k1) `S.union` (subst3 $@ k2)      )

-- | Examples

ex522a = _let "val" (Ref "pi" (Int 0)) (_let "set" (Fn "x" (Var "val" := Var "x"))
            ((Fork (App (Var "set") (Int 2))) `_seq` Deref (Var "val")))
ex522b = _let "val" (Ref "pi" (Int 0)) (_let "set" (Fn "x" (Var "val" := Var "x"))
            (Deref (Var "val") `_seq` (Fork (App (Var "set") (Int 2)))))
ex522c = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 0))
            (_let "f" (Fn "z" (Fork (Var "x" := Int 1 `_seq` Var "y" := Int 1)))
            (Var "x" := Int 2 `_seq` App (Var "f") (Int 0) `_seq` Var "y" := Int 2)))
ex523' = _let "x" (Ref "pi" (Int 1)) (_let "y" (Ref "varpi" (Int 2))
            (_let "lim" (Fn "z" (Deref (Var "z")))
            ((Fork (App (Var "lim") (Var "x")))
                `_seq` Fork (App (Var "lim") (Var "y"))
                `_seq` Fork (App (Var "lim") (Var "x")))))
ex524a = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 1))
            (Fork (Var "x" := Int 1)
                `_seq` Fork (Var "x" := Deref (Var "y"))
                `_seq` Det (Var "y" := Int 2)))
ex524b = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 1))
            (Fork (Var "x" := Int 1)
                `_seq` Fork (Var "x" := Deref (Var "y"))
                `_seq` Det (Var "y" := Deref (Var "x"))))
ex524c = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 1))
            (Det (Fork (Var "x" := Int 2))
                `_seq` (Var "y" := Deref (Var "x"))))
ex524d = _let "x" (Ref "pi" (Int 0)) (_let "y" (Ref "varpi" (Int 1))
            (Det (Fork (Var "y" := Deref (Var "x")))
                `_seq` (Var "x" := Int 2)))
                
-- | Fresh identifiers

class Fresh a where 
    fresh :: State ([Name], s') a
    
instance Fresh Ident where
    fresh = do ((x:xs), s') <- get
               put (xs, s')
               return x
               
instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar a)
               
instance Fresh Eff where
    fresh = do u <- fresh 
               return (EffUnif u)
               
instance Fresh Lvl where
    fresh = do d <- fresh
               return (LvlVar d)
               
instance Fresh DetEff where
    fresh = do e <- fresh
               d <- fresh
               return (e, d)
               
freshIdents = map (\n -> "_{" ++ show n ++ "}") [1..]

-- | Free variables

class FreeVars t where
    ftv :: t -> S.Set Name
               
instance FreeVars Ty where
    ftv (TyInt       ) = S.empty
    ftv (TyFun t _ t') = ftv t `S.union` ftv t'
    ftv (TyVar a     ) = S.singleton a

-- | Substitutions

data Subst = Subst (M.Map Name Ty) (M.Map Name Name) deriving Show

idSubst :: Subst
idSubst = Subst (M.empty) (M.empty)

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (Subst tv1 ev1) (Subst tv2 ev2)
            = Subst (M.unionWith (error "domains not distinct") tv1 tv2)
                    (M.unionWith (error "domains not distinct") ev1 ev2)

class Substitute t where
    ($@) :: Subst -> t -> t
    
instance Substitute Subst where
    subst $@ (Subst tv ev)
        = Subst (M.map (subst $@) tv) (M.map (subst $@) ev)
    
instance Substitute Ty where
    Subst tv _ $@ (TyVar a)
        | Just t <- M.lookup a tv = t
    subst       $@ (TyFun t1 de t2)
        = TyFun (subst $@ t1) (subst $@ de) (subst $@ t2)
    _           $@ x
        = x
        
instance Substitute TyEnv where
    subst $@ env = M.map (\t -> subst $@ t) env

instance Substitute Name where
    Subst _ ev $@ name | Just name' <- M.lookup name ev = name'
                       | otherwise                      = name
                       
instance Substitute Region where
    subst $@ r = S.map (subst $@) r

instance Substitute Eff' where
    subst $@ (EffVar a)    = EffVar (subst $@ a)
    subst $@ (EffDeref r)  = EffDeref (subst $@ r)
    subst $@ (EffAssign r) = EffAssign (subst $@ r)
    subst $@ (EffFork eff) = EffFork (subst $@ eff)
    subst $@ (EffDet eff)  = EffDet (subst $@ eff)

instance Substitute Eff where
    Subst _ ev $@ (EffUnif u) | Just u' <- M.lookup u ev = EffUnif u'
                              | otherwise                = EffUnif u
    subst      $@ (Eff eff)   = Eff (S.map (subst $@) eff)
    
instance Substitute Lvl where
    Subst _ ev $@ (LvlVar u) | Just u' <- M.lookup u ev = LvlVar u'
                             | otherwise                = LvlVar u
    _          $@ x          = x
    
instance (Substitute a, Substitute b) => Substitute (a, b) where
    subst $@ (x, y) = (subst $@ x, subst $@ y)
    
instance Substitute Constr' where
    subst $@ (Eq x y)    = Eq (subst $@ x) (subst $@ y)
    subst $@ (Seq x y z) = Seq (subst $@ x) (subst $@ y) (subst $@ z)
    
instance Substitute Constr where
    subst $@ cs = S.map (subst $@) cs
    

