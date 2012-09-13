{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module TalpinJouvelot where

import Control.Monad
import Control.Monad.State

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S

-- | Syntax

type Ident    = String
type Location = Ident

data Expr
    = Var Ident
    | App Expr  Expr
    | Abs Ident Expr
    | Let Ident Expr Expr
    | New Expr
    | Get Expr
    | Set Expr Expr
    deriving (Eq, Show)
    
data Value
    = Unit
    | Ref Location
    | Closure Ident Expr Env
    deriving (Eq, Show)
    
type Env   = M.Map Ident Value
type TyEnv = M.Map Ident TypeScheme
type Store = M.Map Ident Value

-- | Dynamic Semantics

eval :: Store -> Env -> Expr -> State [Location] (Value, Store)
eval s env (Var x)      | Just v <- M.lookup x env = return (v, s)
                        | otherwise = error "unbound variable"
eval s env (Abs x e)    = return (Closure x e env, s)
eval s env (Let x e e') = do (v, s') <- eval s env e
                             (v', s'') <- eval s' (M.insert x v env) e'
                             return (v', s'')
eval s env (App e e')   = do (Closure x e'' env', s') <- eval s env e
                             (v', s'') <- eval s' env e'
                             (v'', s''') <- eval s'' (M.insert x v' env') e''
                             return (v'', s''')
eval s env (New e)      = do l <- fresh
                             (v, s') <- eval s env e
                             return (Ref l, M.insert l v s')
eval s env (Get e)      = do (Ref l, s') <- eval s env e
                             let Just v = M.lookup l s'
                             return (v, s')
eval s env (Set e e')   = do (Ref l, s') <- eval s env e
                             (v, s'') <- eval s' env e'
                             return (Unit, M.insert l v s'')
                             
eval' e = fst (runState (eval M.empty M.empty e) (map (('?':) . show) [1..]))

-- | Static Semantics

data Region
    = RegCon Ident
    | RegVar Ident
    deriving (Eq, Ord, Show)
    
type Effect = S.Set EffectElem

data EffectElem
    = Init  Region Type
    | Read  Region Type
    | Write Region Type
    | EffVar Ident
    deriving (Eq, Ord, Show)
    
data Type
    = TyUnit
    | TyVar Ident
    | TyRef Region Type
    | TyFun Type Effect Type
    deriving (Eq, Ord, Show)
    
data TypeScheme
    = TypeScheme [Ident] [Ident] [Ident] Type Constrs
    deriving (Eq, Show)
    
data Constr
    = Effect :>: Effect
    deriving (Eq, Ord, Show)

type Constrs = S.Set Constr

-- * Effects 

getEffVar eff
    | S.size eff == 1, EffVar e <- S.findMin eff = e
    | otherwise = error "not an effect variable"

-- * Free variables

-- FIXME: Can we make this into a 2-parameter type class, to avoid having
--        multiple functions, as in Substitutable?
class FreeVars t where
    ftv :: t -> S.Set Ident
    frv :: t -> S.Set Ident
    fev :: t -> S.Set Ident
    fr  :: t -> S.Set Ident
    
instance FreeVars Type where
    ftv TyUnit         = S.empty
    ftv (TyVar a)      = S.singleton a
    ftv (TyRef r t)    = ftv r `S.union` ftv t
    ftv (TyFun t s t') = ftv t `S.union` ftv t' `S.union` ftv s
    
    frv TyUnit         = S.empty
    frv (TyVar a)      = S.empty
    frv (TyRef r t)    = frv r `S.union` frv t
    frv (TyFun t s t') = frv t `S.union` frv t' `S.union` frv s
    
    fev TyUnit         = S.empty
    fev (TyVar a)      = S.empty
    fev (TyRef r t)    = fev r `S.union` fev t
    fev (TyFun t s t') = fev t `S.union` fev t' `S.union` fev s
    
    fr  TyUnit         = S.empty
    fr  (TyVar a)      = S.empty
    fr  (TyRef r t)    = fr r `S.union` fr t
    fr  (TyFun t s t') = fr t `S.union` fr t' `S.union` fr s

instance FreeVars Region where
    ftv (RegCon _) = S.empty
    ftv (RegVar r) = S.empty
    
    frv (RegCon _) = S.empty
    frv (RegVar r) = S.singleton r
    
    fev (RegCon _) = S.empty
    fev (RegVar r) = S.empty

    fr  (RegCon r) = S.singleton r
    fr  (RegVar r) = S.singleton r
    
instance FreeVars EffectElem where
    ftv (Init  r t) = ftv r `S.union` ftv t
    ftv (Read  r t) = ftv r `S.union` ftv t
    ftv (Write r t) = ftv r `S.union` ftv t

    frv (Init  r t) = frv r `S.union` frv t
    frv (Read  r t) = frv r `S.union` frv t
    frv (Write r t) = frv r `S.union` frv t
    
    fev (Init  r t) = fev r `S.union` fev t
    fev (Read  r t) = fev r `S.union` fev t
    fev (Write r t) = fev r `S.union` fev t
    
    fr  (Init  r t) = fr r `S.union` fr t
    fr  (Read  r t) = fr r `S.union` fr t
    fr  (Write r t) = fr r `S.union` fr t
    
instance FreeVars t => FreeVars (S.Set t) where
    ftv = S.unions . map ftv . S.toList
    frv = S.unions . map frv . S.toList
    fev = S.unions . map fev . S.toList
    fr  = S.unions . map fr  . S.toList
    
instance FreeVars TyEnv where   
    ftv = S.unions . map ftv . M.elems
    frv = S.unions . map frv . M.elems
    fev = S.unions . map fev . M.elems
    fr  = S.unions . map fr  . M.elems
    
instance FreeVars TypeScheme where -- FIXME: check this
    ftv (TypeScheme tvs rvs evs t k)
        = (ftv t `S.union` ftv k) `S.difference` (S.fromList tvs)
    frv (TypeScheme tvs rvs evs t k)
        = (frv t `S.union` frv k) `S.difference` (S.fromList rvs)
    fev (TypeScheme tvs rvs evs t k)
        = (fev t `S.union` fev k) `S.difference` (S.fromList evs)
        
instance FreeVars Constr where
    ftv (e :>: e') = ftv e `S.union` ftv e'
    frv (e :>: e') = frv e `S.union` frv e'
    fev (e :>: e') = fev e `S.union` fev e'
    
-- * Substitutions

data Subst = Subst
    { tv_ :: M.Map Ident Type
    , rv_ :: M.Map Ident Region    -- Always a RegVar?
    , ev_ :: M.Map Ident Effect    -- Always an EffVar?
    }

idSubst = Subst M.empty M.empty M.empty

infixr 9 $.

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (Subst tv1 rv1 ev1) (Subst tv2 rv2 ev2)
            = Subst (M.unionWith undefined tv1 tv2)
                    (M.unionWith undefined rv1 rv2)
                    (M.unionWith undefined ev1 ev2)
        
($\) :: Subst -> [Ident] -> Subst
(Subst { tv_ = tv, rv_ = rv, ev_ = ev }) $\ vs
    = Subst { tv_ = prune tv, rv_ = prune rv, ev_ = prune ev }
        where prune m = foldr M.delete m vs
    
class Substitute t where
    ($@) :: Subst -> t -> t
    
instance Substitute Subst where
    subst $@ (Subst tv rv ev) = Subst (M.map (subst $@) tv)
                                      (M.map (subst $@) rv)
                                      (M.map (subst $@) ev)
    
instance Substitute Type where
    subst $@ (TyVar a)      | Just t <- M.lookup a (tv_ subst) = t
    subst $@ (TyRef r t)    = TyRef r (subst $@ t)
    subst $@ (TyFun t s t') = TyFun (subst $@ t) (subst $@ s) (subst $@ t')
    _     $@ x              = x

instance Substitute Region where
    subst $@ (RegVar v) | Just r <- M.lookup v (rv_ subst) = r
    _     $@ x          = x

instance Substitute Effect where
    subst $@ eff = flattenSetOfSets (S.map substElem eff)
        where substElem (EffVar s)  | Just eff <- M.lookup s (ev_ subst) = eff
              substElem (Init  r t) = S.singleton (Init  (subst $@ r) (subst $@ t))
              substElem (Read  r t) = S.singleton (Read  (subst $@ r) (subst $@ t))
              substElem (Write r t) = S.singleton (Write (subst $@ r) (subst $@ t))
              substElem x           = S.singleton x
    
instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env

instance Substitute TypeScheme where
    subst $@ (TypeScheme tvs rvs evs t k)
        = let rsubst = subst $\ tvs
           in TypeScheme tvs rvs evs (rsubst $@ t) (rsubst $@ k)
           
instance Substitute Constr where
    subst $@ (z :>: s) = (subst $@ z) :>: (subst $@ s)
    
instance Substitute Constrs where
    subst $@ k = S.map (subst $@) k

-- * Instantiation

inst :: TypeScheme -> State [Ident] (Type, Constrs)
inst (TypeScheme tvs rvs evs t k)
    = do tvs' <- freshSubst tvs TyVar
         rvs' <- freshSubst tvs RegVar
         evs' <- freshSubst tvs (S.singleton . EffVar)
         return (Subst tvs' rvs' evs' $@ t, k) --FIXME: subst k
    
-- * Generalization
    
gen :: Constrs -> TyEnv -> Effect -> Type -> (TypeScheme, Constrs)
gen k env eff t = let tvs = inEnvAndEff ftv
                      rvs = inEnvAndEff frv
                      evs = inEnvAndEff fev
                   in (TypeScheme tvs rvs evs t k, undefined)
    where
        inEnvAndEff :: (forall t. FreeVars t => t -> S.Set Ident) -> [Ident]
        inEnvAndEff fv = S.toList (fv t `S.difference` (fv env `S.union` fv eff))
                 
-- * Inference algorithm

infer :: TyEnv -> Constrs -> Expr -> State [Ident] (Subst, Type, Effect, Constrs)
infer env k e = do (subst, t, effs, k') <- infer' env k e
                   return (subst, t, error "Observe", k')
                 
infer' :: TyEnv -> Constrs -> Expr -> State [Ident] (Subst, Type, Effect, Constrs)
infer' env k (Var x)
    | Just sigma <- M.lookup x env
        = do (t', k') <- inst sigma
             return (idSubst, t', S.empty, k `S.union` k')
    | otherwise = error "unbound variable"
infer' env k (Abs x e)
    = do _a <- fresh
         _z <- fresh
         let a = TypeScheme [] [] [] (TyVar _a) S.empty
         let z = S.singleton (EffVar _z)
         (subst, t, eff, k') <- infer (M.insert x a env) k e
         return (subst, TyFun (subst $@ (TyVar _a)) z t, S.empty, k' `S.union` S.singleton (z :>: eff))
infer' env k (App e1 e2)
    = do (subst1, t1, eff1, k1) <- infer env k e1
         (subst2, t2, eff2, k2) <- infer (subst1 $@ env) k1 e2
         _a <- fresh
         _z <- fresh
         let a = TyVar _a
         let z = S.singleton (EffVar _z)
         let subst3 = unify k2 (subst2 $@ t1) (TyFun t2 z a)
         let k' = subst3 $@ k2
         let subst = subst3 $. subst2 $. subst1
         return (subst, subst3 $@ a, subst3 $@ (subst2 $@ eff1 `S.union` eff2 `S.union` z), k')
infer' env k (Let x e1 e2)
    = do (subst1, t1, eff1, k1) <- infer env k e1
         let (scheme, k1'') = gen k1 (subst1 $@ env) eff1 t1
         (subst2, t, eff2, k') <- infer (M.insert x scheme (subst1 $@ env)) k1'' e2
         return (subst2 $. subst1, t, subst2 $@ eff1 `S.union` eff2, k')

-- * Unification

unify :: Constrs -> Type -> Type -> Subst
unify k TyUnit TyUnit
    = idSubst
unify k (TyVar a) (TyVar a')
    = Subst (M.singleton a (TyVar a')) M.empty M.empty
unify k (TyVar a) t
    | a `S.member` ftv (bar k $@ t) = error "occurs check"
    | otherwise                     = Subst (M.singleton a t) M.empty M.empty
unify k t (TyVar a)
    | a `S.member` ftv (bar k $@ t) = error "occurs check"
    | otherwise                     = Subst (M.singleton a t) M.empty M.empty
unify k (TyRef (RegVar r) t) (TyRef r' t')
    = let subst = Subst M.empty (M.singleton r r') M.empty
       in unify (subst $@ k) (subst $@ t) (subst $@ t') $. subst
unify k (TyFun ti z tf) (TyFun ti' z' tf') -- FIXME: check if z, z' are really singleton
    = let subst_i = unify k ti ti'
          subst_f = unify (subst_i $@ k) (subst_i $@ tf) (subst_i $@ tf')
          subst   = Subst M.empty M.empty (M.singleton (getEffVar (subst_f $@ subst_i $@ z)) (subst_f $@ subst_i $@ z')) $. subst_f $. subst_i
       in if wf (subst $@ k) then subst else error "not well-formed"
unify _ _ _
    = error "cannot unify"
    
-- * Principal models

bar :: Constrs -> Subst
bar = S.foldr (\(z :>: s) r -> Subst M.empty M.empty (M.singleton (getEffVar z) (r $@ (z `S.union` s))) $. r) idSubst
    
-- * Well-formedness

rng :: Effect -> S.Set (Region, Type)
rng = flattenSetOfSets . S.map rng'
    where rng' (EffVar _ ) = error "variable in range" -- S.singleton
          rng' (Init  r t) = S.singleton (r, t)
          rng' (Read  r t) = S.singleton (r, t)
          rng' (Write r t) = S.singleton (r, t)

wf :: Constrs -> Bool
wf = and . S.toList . mapWithComplement f
    where f (z :>: s) k' = and (S.toList (S.map (\(_, t) -> (getEffVar z) `S.notMember` fev t) (rng (bar k' $@ s))))

-- | Helper functions

-- * Fresh identifiers

fresh :: State [a] a
fresh = do (x:xs) <- get
           put xs
           return x
           
freshSubst :: [Ident] -> (Ident -> t) -> State [Ident] (M.Map Ident t)
freshSubst vs inj
    = do vs' <- replicateM (length vs) fresh
         return (M.fromList (zipWith (\v v' -> (v, inj v')) vs vs'))

-- * Missing

mapWithComplement :: (Ord a, Ord b) => (a -> S.Set a -> b) -> S.Set a -> S.Set b
mapWithComplement f s = S.map g s
    where g x = let (l, r) = S.split x s in f x (l `S.union` r)
    
flattenSetOfSets :: Ord a => S.Set (S.Set a) -> S.Set a
flattenSetOfSets = S.unions . S.toList

-- | Samples

idid = Let "id" (Abs "x" (Var "x")) (App (Var "id") (Var "id"))
