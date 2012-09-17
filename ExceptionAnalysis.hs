{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module ExceptionAnalysis where

import Control.Monad
import Control.Monad.State

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S

-- | Syntax

type Ident     = String
type Label     = String
type Exception = String

data Expr
    = CBool Bool
    | CInt Int
    | Var Ident
    | Abs Label Ident Expr
    | Fix Label Ident Ident Expr
    | App Expr Expr
    | If Expr Expr Expr
    | Let Ident Expr Expr
--  | Op Expr Op Expr
    -- Intermediate expressions
    | Bind TyEnv Expr
    | Close Expr TyEnv
    -- Exceptions
    | Raise Exception
    | Handle Exception Expr Expr
    deriving (Eq, Show)

-- | Static Semantics

data Ann'
    = AnnExn Exception
    | AnnVar Ident
    deriving (Eq, Ord, Show)
    
type Ann = S.Set Ann'
    
data Type
    = TyBool
    | TyInt
    | TyFun Type Ann Type
    | TyVar Ident
    deriving (Eq, Show)

data TyScheme = TyScheme [Ident] [Ident] Type
    deriving (Eq, Show)
    
type TyEnv = M.Map Ident TyScheme

-- * Annotations 

getAnnVar ann
    | S.size ann == 1, AnnVar b <- S.findMin ann
        = b
    | otherwise
        = error "not an annotation variable"

-- * Free variables

class FreeVars t where
    ftv :: t -> S.Set Ident
    fav :: t -> S.Set Ident
    
instance FreeVars Type where
    ftv TyBool          = S.empty
    ftv TyInt           = S.empty
    ftv (TyFun t le t') = ftv t `S.union` ftv t'
    ftv (TyVar a)       = S.singleton a
    
    fav TyBool          = S.empty
    fav TyInt           = S.empty
    fav (TyFun t le t') = fav t `S.union` fav le `S.union` fav t'
    fav (TyVar x)       = S.empty

instance FreeVars TyScheme where
    ftv (TyScheme tvs avs t) = ftv t `S.difference` (S.fromList tvs)
    fav (TyScheme tva avs t) = fav t `S.difference` (S.fromList avs)
    
instance FreeVars TyEnv where
    ftv = S.unions . map ftv . M.elems
    fav = S.unions . map fav . M.elems

instance FreeVars Ann' where
    fav (AnnExn e) = S.empty
    fav (AnnVar b) = S.singleton b
    
instance FreeVars Ann where
    fav = S.unions . map fav . S.toList
    
-- * Substitutions

data Subst = Subst
    { tv_ :: M.Map Ident Type
    , av_ :: M.Map Ident Ann
    }
    
idSubst = Subst M.empty M.empty

infixr 9 $.

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (Subst tv1 av1) (Subst tv2 av2)
            = Subst (M.unionWith (error "type variables not distinct")       tv1 tv2)
                    (M.unionWith (error "annotation variables not distinct") av1 av2)
                    
($\) :: Subst -> [Ident] -> Subst -- FIXME: inefficient
(Subst { tv_ = tv, av_ = av }) $\ vs
    = Subst { tv_ = prune tv, av_ = prune av }
        where prune m = foldr M.delete m vs

class Substitute t where
    ($@) :: Subst -> t -> t
    
instance Substitute Subst where
    subst $@ (Subst tv av) = Subst (M.map (subst $@) tv)
                                   (M.map (subst $@) av)

instance Substitute Type where
    subst $@ (TyVar a)      | Just t <- M.lookup a (tv_ subst) = t
    subst $@ (TyFun t s t') = TyFun (subst $@ t) (subst $@ s) (subst $@ t')
    _     $@ x              = x
    
instance Substitute TyScheme where
    subst $@ (TyScheme tvs avs t)
        = let subst' = subst $\ (tvs ++ avs)
           in TyScheme tvs avs (subst' $@ t)
           
instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env
    
instance Substitute Ann where
    subst $@ ann = flattenSetOfSets (S.map substElem ann)
        where substElem (AnnVar s)  | Just ann <- M.lookup s (av_ subst) = ann
              substElem x           = S.singleton x

-- * Instantiation

inst :: TyScheme -> State [Ident] Type
inst (TyScheme tvs avs t)
    = do tvs' <- freshSubst tvs TyVar
         avs' <- freshSubst avs (S.singleton . AnnVar)
         let subst = Subst tvs' avs'
         return (subst $@ t)
         
-- * Generalization
    
gen :: TyEnv -> Ann -> Type -> TyScheme
gen env ann t = let tvs = inEnvAndAnn ftv
                    avs = inEnvAndAnn fav
                 in TyScheme tvs avs t
    where
        inEnvAndAnn :: (forall t. FreeVars t => t -> S.Set Ident) -> [Ident]
        inEnvAndAnn fv = S.toList (fv t `S.difference` (fv env `S.union` fv ann))

-- * Unification

unify :: Type -> Type -> Subst
unify TyBool TyBool
    = idSubst
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
unify (TyFun ti le tf) (TyFun ti' le' tf') -- FIXME: check if le, le' are singleton
    = let subst_i = unify ti ti'
          subst_f = unify (subst_i $@ tf) (subst_i $@ tf')
          subst   = Subst M.empty (M.singleton (getAnnVar (subst_f $@ subst_i $@ le)) (subst_f $@ subst_i $@ le')) $. subst_f $. subst_i
       in subst
unify _ _
    = error "cannot unify"
    
-- * Inference algorithm

infer :: TyEnv -> Expr -> State [Ident] (Subst, Type, Ann)
infer env (CBool b)
    = return (idSubst, TyBool, S.empty)
infer env (CInt n)
    = return (idSubst, TyInt, S.empty)
infer env (Var x)
    | Just sigma <- M.lookup x env
        = do t <- inst sigma
             return (idSubst, t, S.empty)
    | otherwise = error "unbound variable"
infer env (Abs _ x e)
    = do _a <- fresh
         let a = TyScheme [] [] (TyVar _a)
         (subst, t, ann) <- infer (M.insert x a env) e
         return (subst, TyFun (subst $@ (TyVar _a)) ann t, S.empty)
{- b0 == ann0 ?
infer env (Fix _ f x e0)
    = do ax <- fresh
         a0 <- fresh
         b0 <- fresh
         (subst0, t0, ann0) <- infer (M.insert f (TyFun ax b0 a0) (M.insert x ax env)) e0
         let subst1 = unify t0 (subst0 $@ a0)
         return (subst1 $. subst0, TyFun (subst1 $@ subst0 $@ ax) (subst1 $@ subst0 $@ ann0) (subst1 $@ t0), S.empty)
-}
infer env (App e1 e2)
    = do (subst1, t1, ann1) <- infer env e1
         (subst2, t2, ann2) <- infer env e2
         a <- fresh
         b <- fresh
         let subst3 = unify (subst2 $@ t1) (TyFun t2 b a)
         let subst  = subst3 $. subst2 $. subst1
         return (subst, subst3 $@ a, subst3 $@ (subst2 $@ ann1 `S.union` ann2 `S.union` b))
infer env (If e0 e1 e2)
    = do (subst0, t0, ann0) <- infer env e0
         (subst1, t1, ann1) <- infer (subst0 $@ env) e1
         (subst2, t2, ann2) <- infer (subst1 $@ subst0 $@ env) e2
         let subst3 = unify (subst2 $@ subst1 $@ t0) TyBool
         let subst4 = unify (subst3 $@ t2) (subst3 $@ subst2 $@ t1)
         return (subst4 $. subst3 $. subst2 $. subst1 $. subst0
                ,subst4 $@ subst3 $@ t2
                ,(subst4 $@ subst3 $@ subst2 $@ subst1 $@ ann0)
                    `S.union` (subst4 $@ subst3 $@ subst2 $@ ann1)
                    `S.union` (subst4 $@ subst3 $@ ann2)
                )
infer env (Let x e1 e2)
    = do (subst1, t1, ann1) <- infer env e1
         let sigma1 = gen (subst1 $@ env) ann1 t1
         (subst2, t2, ann2) <- infer (M.insert x sigma1 (subst1 $@ env)) e2
         return (subst2 $. subst1, t2, subst2 $@ ann1 `S.union` ann2)
infer env (Raise s)
    = do t <- fresh
         return (idSubst, t, S.singleton (AnnExn s))
infer env (Handle s e1 e2)
    = do (subst1, t1, ann1) <- infer env e1
         (subst2, t2, ann2) <- infer (subst1 $@ env) e2
         let subst3 = unify t1 (subst1 $@ t1)
         return (subst3 $. subst2 $. subst1, subst3 $@ t2, (subst3 $@ subst2 $@ ann1) `S.union` mask s (subst3 $@ ann2))
         
-- * Effect masking

-- Very approxiate version from NNH p. 330 (does not mask annotation variables)
mask :: Exception -> Ann -> Ann
mask ex = S.filter (/= (AnnExn ex))

-- | Helper functions

-- * Fresh identifiers

class Fresh t where
    fresh :: State [Ident] t
    
instance Fresh Ident where
    fresh = do (x:xs) <- get
               put xs
               return x
               
instance Fresh Type where
    fresh = do ident <- fresh
               return (TyVar ident)
               
instance Fresh TyScheme where
    fresh = do t <- fresh
               return (TyScheme [] [] t)
               
instance Fresh Ann' where
    fresh = do ident <- fresh
               return (AnnVar ident)
               
instance Fresh Ann where
    fresh = do b <- fresh
               return (S.singleton b)
               
freshIdents = map (('?':) . show) [1..]
           
freshSubst :: [Ident] -> (Ident -> t) -> State [Ident] (M.Map Ident t)
freshSubst vs inj
    = do vs' <- replicateM (length vs) fresh
         return (M.fromList (zipWith (\v v' -> (v, inj v')) vs vs'))

-- * Missing

flattenSetOfSets :: Ord a => S.Set (S.Set a) -> S.Set a
flattenSetOfSets = S.unions . S.toList

