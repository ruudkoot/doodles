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
    deriving (Eq, Show)
    
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
    ftv TyBool        = S.empty
    ftv TyInt         = S.empty
    ftv TyFun t le t' = ftv t `S.union` ftv t'
    ftv TyVar a       = S.singleton a
    
    fav TyBool        = S.empty
    fav TyInt         = S.empty
    fav TyFun t le t' = fav t `S.union` fav le `S.union` fav t'
    fav TyVar x       = S.empty

instance FreeVars TyScheme where
    ftv (TyScheme tvs avs t) = ftv t `S.difference` (S.fromList tvs)
    fav (TyScheme tva avs t) = fav t `S.difference` (s.fromList avs)
    
instance FreeVars TyEnv where
    ftv = S.unions . map ftv . M.elems
    fav = S.unions . map fav . M.elems

instance FreeVars Ann' where
    fav AnnExn e = S.empty
    fav AnnVar b = S.singleton b
    
instance FreeVars Ann where
    fav = S.unions . map fav . S.toList
    
-- * Substitutions

data Subst = Subst
    { tv_ :: M.Map Ident Type
    , av_ :: M.Map Ident Ann
    }
    
idSubst = Subst M.empty M.empty

infixr $.


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
    
instance Substitute TypeScheme where
    subst $@ (TypeScheme tvs avs t)
        = let subst' = subst $\ (tvs ++ avs)
           in TypeScheme tvs avs (subst' $@ t)
           
instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env
    
instance Substitute Ann where
    subst $@ ann = flattenSetOfSets (S.map substElem ann)
        where substElem (AnnVar s)  | Just ann <- M.lookup s (av_ subst) = ann
              substElem x           = S.singleton x

-- * Instantiation

inst :: TyScheme -> State [Ident] Type
inst (TypeScheme tvs avs t)
    = do tvs' <- freshSubst tvs TyVar
         avs' <- freshSubst avs (S.singleton . AnnVar)
         let subst = Subst tvs' avs'
         return (subst $@ t)
         
-- * Generalization
    
gen :: TyEnv -> Ann -> Type -> TyScheme
gen env ann t = let tvs = inEnvAndAnn ftv
                    avs = inEnvAndAnn fav
                 in TypeScheme tvs avs t
    where
        inEnvAndAnn :: (forall t. FreeVars t => t -> S.Set Ident) -> [Ident]
        inEnvAndAnn fv = S.toList (fv t) `S.difference` (fv env `S.union` fv ann)

-- * Unification

unify :: Type -> Type -> Subst
unify TyUnit TyUnit
    = idSubst
unify (TyVar a) (TyVar a')
    = Subst (M.singleton a (TyVar a')) M.empty
unify (TyVar a) t
    | a `S.member` ftv ) = error "occurs check"
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

-- | Helper functions

-- * Fresh identifiers

fresh :: State [a] a
fresh = do (x:xs) <- get
           put xs
           return x
           
freshIdents = map (('?':) . show) [1..]
           
freshSubst :: [Ident] -> (Ident -> t) -> State [Ident] (M.Map Ident t)
freshSubst vs inj
    = do vs' <- replicateM (length vs) fresh
         return (M.fromList (zipWith (\v v' -> (v, inj v')) vs vs'))

-- * Missing

flattenSetOfSets :: Ord a => S.Set (S.Set a) -> S.Set a
flattenSetOfSets = S.unions . S.toList

