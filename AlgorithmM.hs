{-# LANGUAGE TupleSections #-}

module AlgorithmM where

import Control.Monad
import Control.Monad.State
import Data.List

type Ident
    = String

data Expr
    = Con
    | Var Ident
    | Lam Ident Expr
    | App Expr Expr
    | Let Ident Expr Expr
    | Fix Ident Ident Expr
    deriving (Eq, Ord, Show)
    
data Type
    = TyCon
    | TyVar Ident
    | TyFun Type Type
    deriving (Eq, Ord, Show)
    
data TypeScheme
    = TypeScheme [Ident] Type
    deriving (Eq, Ord, Show)
    
type TypeEnv
    = [(Ident, TypeScheme)]
    
type Subst
    = [(Ident, Type)]

idSubst :: Subst
idSubst = []

class FTV t where
    ftv :: t -> [Ident]

class Substitutable t where
    ($@) :: Subst -> t -> t

instance FTV Type where
    ftv  TyCon      = []
    ftv (TyVar x)   = [x]
    ftv (TyFun a b) = ftv a `union` ftv b

instance Substitutable Type where
    _               $@     TyCon      = TyCon
    []              $@    (TyVar x)   = TyVar x
    ((x, ty):theta) $@ tv@(TyVar y)   | x == y    = ty
                                      | otherwise = theta $@ tv
    theta           $@    (TyFun a b) = TyFun (theta $@ a) (theta $@ b)

instance Substitutable TypeScheme where
    theta $@ (TypeScheme as ty) = TypeScheme as ((theta \\\ as) $@ ty)
    
    
(\\\) :: Subst -> [Ident] -> Subst
xs \\\ ys = deleteFirstsBy (\(x,_) (y,_) -> x == y) xs (map (,undefined) ys)

    
fresh :: State [a] a
fresh = do (x:xs) <- get
           put xs
           return x    
           
freshTyVar :: State [Ident] Type
freshTyVar = fresh >>= return . TyVar

freshTyScheme :: State [Ident] TypeScheme
freshTyScheme = freshTyVar >>= return . TypeScheme []

freshIdents = map (('?':) . show) [1..]

algorithmW :: TypeEnv -> Expr -> State [Ident] (Subst, Type)
algorithmW gamma Con
    = return (idSubst, TyCon)
algorithmW gamma (Var x)
    | Just sigma <- lookup x gamma
        = do ty <- inst sigma
             return (idSubst, ty)
    | otherwise
        = error ("Variable \"" ++ show x
                               ++ "\" not found in environment "
                               ++ show gamma)
algorithmW gamma (Lam x e)
    = do b         <- freshTyVar
         (s1, ty1) <- algorithmW ((x, gen b) : gamma) e
         return (s1, TyFun (s1 $@ b) ty1)
algorithmW gamma (App f x)
    = do (s1, ty1) <- algorithmW        gamma  f
         (s2, ty2) <- algorithmW (s1 $@ gamma) x
         b         <- freshTyVar
         s3        <- unify (s2 $@ ty1) (TyFun ty2 b)
         return (s3 $. s2 $. s1, s3 $@ b)        

inst :: TypeScheme -> State [Ident] Type
inst (TypeScheme as ty) = do bs <- replicateM (length as) freshTyVar
                             return (zip as bs $@ ty)
                             
gen :: Type -> TypeScheme
gen ty = TypeScheme (ftv ty) ty

main = do let gamma0           = []
          let e                = Lam "x" (Var "x")
          let ((theta, ty), _) = runState (algorithmW gamma0 e) freshIdents
          print (theta $@ ty)
