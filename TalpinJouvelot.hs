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
    = Effect :<: Effect
    deriving (Eq, Ord, Show)

type Constrs = S.Set Constr

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
    ftv (e :<: e') = ftv e `S.union` ftv e'
    frv (e :<: e') = frv e `S.union` frv e'
    fev (e :<: e') = fev e `S.union` fev e'
    
-- * Substitutions

type Subst s = M.Map Ident s

idSubst = M.empty
    
class Substitute s t where
    ($@) :: Subst s -> t -> t
    
instance Substitute Type Type where
    subst $@ (TyVar a)      | Just t <- M.lookup a subst = t
    subst $@ (TyRef r t)    = TyRef r (subst $@ t)
    subst $@ (TyFun t s t') = TyFun (subst $@ t) (subst $@ s) (subst $@ t')
    _     $@ x              = x

instance Substitute Region Type where
    subst $@ (TyRef r t)    = TyRef r (subst $@ t)
    subst $@ (TyFun t s t') = TyFun (subst $@ t) (subst $@ s) (subst $@ t')
    _     $@ x              = x

instance Substitute EffectElem Type where
    subst $@ (TyRef r t)    = TyRef r (subst $@ t)
    subst $@ (TyFun t s t') = TyFun (subst $@ t) (subst $@ s) (subst $@ t')
    _     $@ x              = x
    
instance Substitute Type Region where
    _     $@ x          = x

instance Substitute Region Region where
    subst $@ (RegVar v) | Just r <- M.lookup v subst = r
    _     $@ x          = x

instance Substitute EffectElem Region where
    _     $@ x          = x
   
instance Substitute Type EffectElem where
    subst $@ (Init  r t) = Init  (subst $@ r) (subst $@ t)
    subst $@ (Read  r t) = Read  (subst $@ r) (subst $@ t)
    subst $@ (Write r t) = Write (subst $@ r) (subst $@ t)
    _     $@ x           = x
    
instance Substitute Region EffectElem where
    subst $@ (Init  r t) = Init  (subst $@ r) (subst $@ t)
    subst $@ (Read  r t) = Read  (subst $@ r) (subst $@ t)
    subst $@ (Write r t) = Write (subst $@ r) (subst $@ t)
    _     $@ x           = x
    
instance Substitute EffectElem EffectElem where
    subst $@ (EffVar s)  | Just eff <- M.lookup s subst = eff
    subst $@ (Init  r t) = Init  (subst $@ r) (subst $@ t)
    subst $@ (Read  r t) = Read  (subst $@ r) (subst $@ t)
    subst $@ (Write r t) = Write (subst $@ r) (subst $@ t)
    _     $@ x           = x

instance Substitute Type Effect where
    subst $@ eff = S.map (subst $@) eff
    
instance Substitute Region Effect where
    subst $@ eff = S.map (subst $@) eff
    
instance Substitute EffectElem Effect where
    subst $@ eff = S.map (subst $@) eff

-- * Instantiation

inst :: TypeScheme -> State [Ident] (Type, Constrs)
inst (TypeScheme tvs rvs evs t k)
    = do tsubst <- freshSubst tvs TyVar
         rsubst <- freshSubst tvs RegVar
         esubst <- freshSubst tvs EffVar
         return (esubst $@ (rsubst $@ (tsubst $@ t)), k) --FIXME: subst k
    
-- * Generalization
    
gen :: Constrs -> TyEnv -> Effect -> Type -> TypeScheme
gen k env eff t = let tvs = inEnvAndEff ftv
                      rvs = inEnvAndEff frv
                      evs = inEnvAndEff fev
                   in TypeScheme tvs rvs evs t k
    where
        inEnvAndEff :: (forall t. FreeVars t => t -> S.Set Ident) -> [Ident]
        inEnvAndEff fv = S.toList (fv t `S.difference` (fv env `S.union` fv eff))
                 
-- * Inference algorithm

type Observables = ()
                 
infer :: TyEnv -> Constrs -> Expr -> State [Ident] (Subst Type,  Type, Observables, Constrs)
infer env k e = do (subst, t, effs, k') <- infer' env k e
                   return (subst, t, error "Observe", k')
                 
infer' :: TyEnv -> Constrs -> Expr -> State [Ident] (Subst Type, Type, Effect, Constrs)
infer' env k (Var x)
    | Just sigma <- M.lookup x env
        = do (t', k') <- inst sigma
             return (idSubst, t', S.empty, k `S.union` k')
    | otherwise = error "unbound variable"
infer' env k (Abs x e)
    = do a <- fresh
         z <- fresh
         (subst, t, eff, k) <- infer (M.insert x a env) k e
         return (subst, TyFun (subst $@ a) (EffVar z) t, S.empty, k' `S.union` S.singleton (eff :<: EffVar z))


-- | Monadic helpers

fresh :: State [a] a
fresh = do (x:xs) <- get
           put xs
           return x
           
freshSubst :: [Ident] -> (Ident -> t) -> State [Ident] (Subst t)
freshSubst vs inj
    = do vs' <- replicateM (length vs) fresh
         return (M.fromList (zipWith (\v v' -> (v, inj v')) vs vs'))
           
-- | Samples

idid = Let "id" (Abs "x" (Var "x")) (App (Var "id") (Var "id"))
