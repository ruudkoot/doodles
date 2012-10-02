{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}

module Main (main) where

-- PERFORMANCE: commutativity and associativity of S.union (bigset `S.union` smallset)
--              TyScheme, quantified variables as list or set?

import           Control.Monad
import           Control.Monad.State

import qualified Data.Graph as G
import qualified Data.List  as L
import qualified Data.Map   as M
import           Data.Maybe
import qualified Data.Set   as S
import qualified Data.Tree  as T

import qualified Equiv      as E

-- deriving instance Ord a => Ord (UF.Point a)

main = do let expr = exB
          let ((s, t, b, c), (_, msgs))
               = runState (infer M.empty expr) (freshIdents, [])
          putStrLn $ show msgs
          putStrLn $ "Type        : " ++ show t
          putStrLn $ "Behaviour   : " ++ show b
          putStrLn $ "Constraints : " ++ show c
          putStrLn $ "Substitution: " ++ show s
          
exA = Let "id" (Fn "x" (Var "x")) (Var "id")
exB = Let "id" (Fn "x" (Var "x")) (Var "id" `App` Var "id")
          
ex230 = Fn "f" (Let "id" (Fn "y" ((If (Con (Bool True)) (Var "f") (Fn "x" (Con Sync `App` Con Send `App` (Con Pair `App` (Con Channel) `App` (Var "y")) `_seq` (Var "x")))) `_seq` (Var "y"))) (Var "id" `App` Var "id"))

_seq :: Expr -> Expr -> Expr
_seq e1 e2 = Con Snd `App` (Con Pair `App` e1 `App` e2)

-- | Syntax

type Name  = String
type Ident = Name

data Expr
    = Con Con
    | Var Ident
    | Fn  Ident Expr
    | App Expr  Expr
    | Let Ident Expr  Expr
    | Rec Ident Ident Expr
    | If  Expr  Expr  Expr
    deriving (Eq, Ord, Show)
    
data Con
    = Unit
    | Bool Bool
    | Int  Int
    | Plus | Times   | Eq
    | Pair | Fst     | Snd
    | Nil  | Cons    | Hd   | Tl      | IsNil
    | Send | Receive | Sync | Channel | Fork
    deriving (Eq, Ord, Show)

-- | Static semantics

data Ty
    = TyVar  Ident
    | TyUnit
    | TyInt
    | TyBool
    | TyPair Ty Ty
    | TyList Ty
    | TyFun  Ty Be Ty
    | TyChan Ty
    | TyCom  Ty Be
    deriving (Eq, Ord, Show)

data Be
    = BeUnif Name
    | Be     (S.Set Be')
    deriving (Eq, Ord, Show)
    
injBe  (BeUnif u)      = Be (S.singleton (BeVar u))
joinBe (Be b1) (Be b2) = Be (b1 `S.union` b2)

data Be'
    = BeChan Ty
    | BeVar  Ident
    deriving (Eq, Ord, Show)

type Constr = S.Set Constr'

data Constr'
    = Ty :<:  Ty
    | Be :<*: Be
    deriving (Eq, Ord, Show)
    
data TyScheme = Forall [Ident] [Ident] Constr Ty deriving (Eq, Ord, Show)

injTS = Forall [] [] S.empty

type TyEnv = M.Map Ident TyScheme

-- * Inference

infer env e
    = do (s1, t1, b1, c1) <- infer' env e
         (s2, c2) <- force c1
         -- (s2, c2) <- return (s1, c1)
         (c3, t3, b3) <- return (c2, t1, b1) -- reduce
         return (s2 $. s1, t3, b3, c3)

infer' :: TyEnv -> Expr -> State ([Name], [String]) (Subst, Ty, Be, Constr)
infer' env (Con c)
    = do (s, t, b, c) <- inst (typeOf c)
         t' <- mkSimple t
         return (s, t', b, c)
infer' env (Var x)
    | Just ts <- M.lookup x env = inst ts
    | otherwise                 = error "variable not in scope"
infer' env (Fn x e0)
    = do a <- fresh
         (s0, t0, b0, c0) <- infer (M.insert x (injTS a) env) e0
         b <- fresh
         return ( s0, TyFun (s0 $@ a) b t0, Be S.empty
                , c0 `S.union` S.fromList [b0 :<*: b] )
infer' env (App e1 e2)
    = do (s1, t1, b1, c1) <- infer env e1
         (s2, t2, b2, c2) <- infer (s1 $@ env) e2
         (a, b) <- fresh
         return ( s2 $. s1, a, s2 $@ b1 `joinBe` b2 `joinBe` injBe b
                , s2 $@ c1 `S.union` c2
                           `S.union` S.fromList [s2 $@ t1 :<: TyFun t2 b a] )
infer' env (Let x e1 e2)
    = do (s1, t1, b1, c1) <- infer env e1
         let ts1 = gen (s1 $@ env) b1 c1 t1
         (s2, t2, b2, c2) <- infer (M.insert x ts1 (s1 $@ env)) e2
         return ( s2 $. s1, t2, s2 $@ b1 `joinBe` b2, s2 $@ c2 `S.union` c1 )
infer' env (Rec f x e0)
    | f == x = error "binders not distinct"
    | otherwise
        = do (a1, b, a2) <- fresh
             (s0, t0, b0, c0) <- infer (M.insert x (injTS a1)
                                            (M.insert f (injTS (TyFun a1 b a2)) env)) e0
             return ( s0, s0 $@ TyFun a1 b a2, Be S.empty
                    , c0 `S.union` S.fromList [b0 :<*: (s0 $@ b), t0 :<: (s0 $@ a2)] )
infer' env (If e0 e1 e2)
    = do (s0, t0, b0, c0) <- infer env e0
         (s1, t1, b1, c1) <- infer (s0 $@ env) e1
         (s2, t2, b2, c2) <- infer (s1 $@ s0 $@ env) e2
         a <- fresh
         return ( s2 $. s1 $. s0, a, s2 $@ s1 $@ b0 `joinBe` (s2 $@ b1) `joinBe` b2
                , s2 $@ s1 $@ c0 `S.union` (s2 $@ c1) `S.union` c2 `S.union`
                    S.fromList [s2 $@ s1 $@ t0 :<: TyBool, s2 $@ t1 :<: a, t2 :<: a] )

-- * Forcing/matching

force :: Constr -> State ([Name], [String]) (Subst, Constr)
force c = do message "-----------------"
             (s', c', equiv') <- rewrite (idSubst, c, eqc c)
             if atomic c' then return (s', c') else error "forcing failed"

atomic :: Constr -> Bool
atomic = and . map atomic' . S.toList
    where atomic' (TyVar  _ :<:  TyVar  _) = True
          atomic' (Be chan  :<*: BeUnif _) | [BeChan _] <- S.toList chan = True
          atomic' (BeUnif _ :<*: BeUnif _) = True
          atomic' _                        = False

rewrite :: (Subst, Constr, E.Equiv Name) -> State ([Name], [String]) (Subst, Constr, E.Equiv Name)
rewrite (s, c, e)
    = do dc <- process decompose c
         maybeMatch <- process2 (s, dc, e)
         message "R>>"
         case maybeMatch of
            Nothing            -> return (s, dc, e)
            Just (s', dc', e') -> rewrite (s', dc', e')
         

process :: (Ord a, Show a) => (a -> Maybe (S.Set a)) -> S.Set a -> State ([Name], [String]) (S.Set a)
process f x = process' S.empty x
    where process' u w
            = do message "P>>"
                 case S.minView w of
                   Nothing       -> return u
                   Just (c', w') -> case f c' of
                                       Nothing  -> process' (c' `S.insert` u) w'
                                       Just w'' -> process' u (w' `S.union` w'')

decompose :: Constr' -> Maybe Constr
decompose (Be bs :<*: b)  -- \emptyset and \cup
    = Just $ S.map (\b' -> (Be (S.singleton b') :<*: b)) bs
decompose (TyUnit :<: TyUnit)
    = Just $ S.empty
decompose (TyBool :<: TyBool)
    = Just $ S.empty
decompose (TyInt :<: TyInt)
    = Just $ S.empty
decompose (TyPair t1 t2 :<: TyPair t3 t4)
    = Just $ S.fromList [t1 :<: t3, t2 :<: t4]
decompose (TyList t1 :<: TyList t2)
    = Just $ S.fromList [t1 :<: t2]
decompose (TyChan t1 :<: TyChan t2)
    = Just $ S.fromList [t1 :<: t2, t2 :<: t1]
decompose (TyCom  t1 b1 :<: TyCom  t2 b2)
    = Just $ S.fromList [t1 :<: t2, b1 :<*: b2]
decompose (TyFun t1 b1 t2 :<: TyFun t3 b2 t4)
    = Just $ S.fromList [t3 :<: t1, b1 :<*: b2, t2 :<: t4]
decompose _
    = Nothing

process2 :: (Subst, Constr, E.Equiv Name) -> State ([Name], [String]) (Maybe (Subst, Constr, E.Equiv Name))
process2 = process' S.empty
    where process' u (s, w, e)
            = case S.minView w of
                Nothing       -> return Nothing
                Just (c', w') -> do maybeSCE <- mrml (s, u `S.union` w', e) c'
                                    case maybeSCE of 
                                        Nothing -> process' (c' `S.insert` u) (s, w', e)
                                        result  -> return result

mrml :: (Subst, Constr, E.Equiv Name) -> Constr' -> State ([Name], [String]) (Maybe (Subst, Constr, E.Equiv Name))
mrml (s, c, equiv) (t :<: TyVar a)
    = do maybeSE <- m a t equiv
         case maybeSE of
            Nothing          -> return $ Nothing
            Just (r, equiv') -> return $ Just (r $@ s, S.insert ((r $@ t) :<: (r $@ (TyVar a))) (r $@ c), equiv')
mrml (s, c, equiv) (TyVar a :<: t)
    = do maybeSE <- m a t equiv
         case maybeSE of
            Nothing          -> return $ Nothing
            Just (r, equiv') -> return $ Just (r $@ s, S.insert ((r $@ (TyVar a)) :<: (r $@ t)) (r $@ c), equiv')
mrml _             _
    = return Nothing

eqc :: Constr -> E.Equiv Name
eqc = S.foldr E.insert E.empty . ftv

m :: Name -> Ty -> E.Equiv Name -> State ([Name], [String]) (Maybe (Subst, E.Equiv Name))
m a t equiv
    = do let as     = E.equivalenceClass equiv a
         let n      = S.size as
         let (as0, bs0)
                    = shGet t
         let m      = length as0
         ass        <- replicateM n (replicateM m              fresh)
         bss        <- replicateM n (replicateM (length (bs0)) fresh)
         let r      = Subst (M.fromList
                                (zipWith3 (\a as bs -> (a, shPut t (as, bs)))
                                          (S.toList as) ass bss))
                            M.empty
         let equiv' = undefined
         if S.null (as `S.intersection` fv t)
            then return (Just (r, equiv'))
            else return Nothing

-- FIXME: i don't think the order matters, as long as we do it consistently
shGet :: Ty -> ([Name], [Be])
shGet (TyVar a)        = ([a], [])
shGet TyUnit           = ([], [])
shGet TyBool           = ([], [])
shGet TyInt            = ([], [])
shGet (TyPair t1   t2) = shGet t1 +++ shGet t2
shGet (TyFun  t1 b t2) = shGet t1 +++ ([], [b]) +++ shGet t2
shGet (TyList t      ) = shGet t
shGet (TyChan t      ) = shGet t
shGet (TyCom  t  b   ) = shGet t +++ ([], [b])

shPut :: Ty -> ([Name], [Be]) -> Ty
shPut t (as, bs) = let (t', [], []) = shPut' t (as, bs) in t'

shPut' :: Ty -> ([Name], [Be]) -> (Ty, [Name], [Be])
shPut' (TyVar _)       (a:as, bs) = (TyVar a, as, bs)
shPut' TyUnit          (  as, bs) = (TyUnit , as, bs)
shPut' TyBool          (  as, bs) = (TyBool , as, bs)
shPut' TyInt           (  as, bs) = (TyInt  , as, bs)
shPut' (TyPair t1 t2)  (as0, bs0) = let (t1', as1, bs1) = shPut' t1 (as0, bs0)
                                        (t2', as2, bs2) = shPut' t2 (as1, bs1)
                                     in (TyPair t1' t2', as2, bs2)
shPut' (TyFun t1 b t2) (as0, bs0) = let (t1', as1, b':bs1) = shPut' t1 (as0, bs0)
                                        (t2', as2,    bs2) = shPut' t2 (as1, bs2)
                                     in (TyFun t1' b' t2', as2, bs2)
shPut' (TyList t)      (as, bs)   = let (t', as', bs') = shPut' t (as, bs)
                                     in (TyList t', as', bs')
shPut' (TyChan t)      (as, bs)   = let (t', as', bs') = shPut' t (as, bs)
                                     in (TyChan t', as', bs')
shPut' (TyCom t b)     (as, bs)   = let (t', as', b':bs') = shPut' t (as, bs)
                                     in (TyCom t' b', as', bs')

(+++) :: ([a], [b]) -> ([a], [b]) -> ([a], [b])
(xs1, ys1) +++ (xs2, ys2) = (xs1 ++ xs2, ys1 ++ ys2)

-- * Primitive types

typeOf Unit
    = injTS $ TyUnit
typeOf (Bool _)
    = injTS $ TyBool
typeOf (Int  _)
    = injTS $ TyInt
typeOf Plus
    = injTS $ TyFun (TyPair TyInt TyInt) (Be S.empty) TyInt
typeOf Times    
    = injTS $ TyFun (TyPair TyInt TyInt) (Be S.empty) TyInt
typeOf Eq
    = injTS $ TyFun (TyPair TyInt TyInt) (Be S.empty) TyBool
typeOf Pair
    = Forall ["a1", "a2"] [] S.empty
        (TyFun (TyVar "a1") (Be S.empty) (TyFun (TyVar "a2") (Be S.empty)
            (TyPair (TyVar "a1") (TyVar "a2"))))
typeOf Fst
    = Forall ["a1", "a2"] [] S.empty
        (TyFun (TyPair (TyVar "a1") (TyVar "a2")) (Be S.empty) (TyVar "a1"))
typeOf Snd
    = Forall ["a1", "a2"] [] S.empty
        (TyFun (TyPair (TyVar "a1") (TyVar "a2")) (Be S.empty) (TyVar "a2"))
typeOf Nil      = undefined
typeOf Cons     = undefined
typeOf Hd       = undefined
typeOf Tl       = undefined
typeOf IsNil    = undefined
typeOf Send
    = Forall ["a"] [] S.empty
        (TyFun (TyPair (TyChan (TyVar "a")) (TyVar "a")) (Be S.empty)
            (TyCom (TyVar "a") (Be S.empty)))
typeOf Receive
    = Forall ["a"] [] S.empty
        (TyFun (TyChan (TyVar "a")) (Be S.empty) (TyCom (TyVar "a") (Be S.empty)))
typeOf Sync
    = Forall ["a"] ["b"] S.empty
        (TyFun (TyCom (TyVar "a") (BeUnif "b")) (BeUnif "b") (TyVar "a"))
typeOf Channel
    = Forall ["a"] ["b"]
        (S.singleton (Be (S.singleton (BeChan (TyVar "a"))) :<*: BeUnif "b"))
        (TyFun TyUnit (BeUnif "b") (TyChan (TyVar "a")))
typeOf Fork
    = Forall ["a"] ["b"] S.empty
        (TyFun (TyFun TyUnit (BeUnif "b") (TyVar "a")) (Be S.empty) TyUnit)

mkSimple t@(TyVar _)       = return t
mkSimple t@TyUnit          = return t
mkSimple t@TyInt           = return t
mkSimple t@TyBool          = return t
mkSimple t@(TyPair t1 t2)  = do t1' <- mkSimple t1
                                t2' <- mkSimple t2
                                return (TyPair t1' t2')
mkSimple   (TyList t)      = do t' <- mkSimple t
                                return (TyList t')
mkSimple   (TyFun t1 b t2) = do b' <- mkSimple' b
                                t1' <- mkSimple t1
                                t2' <- mkSimple t2
                                return (TyFun t1' b' t2')
mkSimple   (TyChan t)      = do t' <- mkSimple t
                                return (TyChan t')
mkSimple   (TyCom t b)     = do b' <- mkSimple' b
                                t' <- mkSimple t
                                return (TyCom t' b')

mkSimple' b@(BeUnif _)        = return b
mkSimple' (Be bs) | S.null bs = fresh
                  | otherwise = error "type not simplifiable"

-- * Instantiation

inst (Forall as bs c t)
    = do as' <- replicateM (length as) fresh
         bs' <- replicateM (length bs) fresh
         let r = Subst (M.fromList (zipWith (\a a' -> (a, TyVar a')) as as'))
                       (M.fromList (zip                              bs bs'))
         return (idSubst, r $@ t, Be S.empty, r $@ c)

-- * Generalization
         
gen env b c t
    = let abs = (fv t `biClose` c) `S.difference` ((fv env `S.union` fv b) `downClose` c)
          as  = abs `S.intersection` (ftv t `S.union` ftv env `S.union` ftv b)
          bs  = abs `S.intersection` (fbv t `S.union` fbv env `S.union` fbv b)
          c0  = S.filter f c
            where f (g1 :<: g2)  = not (S.null ((fv g1 `S.union` fv g2) `S.intersection` abs))
                  f (g1 :<*: g2) = not (S.null ((fv g1 `S.union` fv g2) `S.intersection` abs))
       in Forall (S.toList as) (S.toList bs) c0 t

-- * Closures

upClose, downClose, biClose :: S.Set Name -> Constr -> S.Set Name

upClose x c
    = let f0 = S.foldr closeHelper M.empty c
          fc = transitiveClosure (reflexiveClosure f0)
       in S.filter (\k -> not (S.null (fromMaybe (error "upClose") (M.lookup k fc) `S.intersection` x))) (M.keysSet fc)
       
downClose x c
    = let f0 = S.foldr closeHelper M.empty c
          fc = transitiveClosure (reflexiveClosure f0)
       in S.filter (\k -> not (S.null (fromMaybe (error "downClose") (M.lookup k fc) `S.intersection` x))) (M.keysSet fc)

biClose x c
    = let f0 = S.foldr closeHelper M.empty c
          fc = transitiveClosure (symmetricClosure (reflexiveClosure f0))
       in S.filter (\k -> not (S.null (fromMaybe (error "biClose") (M.lookup k fc) `S.intersection` x))) (M.keysSet fc)
       
closeHelper (g1 :<:  g2) r = S.foldr (\x -> M.insertWith S.union x (fv g2)) r (fv g1)
closeHelper (g1 :<*: g2) r = S.foldr (\x -> M.insertWith S.union x (fv g2)) r (fv g1)

-- * Reflexive transitive closure

reflexiveClosure :: Ord a => M.Map a (S.Set a) -> M.Map a (S.Set a)
reflexiveClosure m
    = foldr (\k -> M.insertWith S.union k (S.singleton k)) m (M.keys m)
    -- PERFORMANCE: Change S.union to S.insert/S.singleton depending on existence
    
symmetricClosure :: Ord a => M.Map a (S.Set a) -> M.Map a (S.Set a)
symmetricClosure m
    = M.foldrWithKey (\k v r -> S.foldr (\v' r' -> M.insertWith S.union v' (S.singleton k) r') r v) m m

transitiveClosure :: Ord a => M.Map a (S.Set a) -> M.Map a (S.Set a)
transitiveClosure m
    = foldr reconstruct m . reverse . G.stronglyConnComp . toEdgeList $ m

toEdgeList :: M.Map k (S.Set a) -> [((k, S.Set a), k, [a])]
toEdgeList
    = M.foldrWithKey (\k v -> (:) ((k, v), k, S.toList v)) []

reconstruct :: Ord a => G.SCC (a, S.Set a) -> M.Map a (S.Set a) -> M.Map a (S.Set a)
reconstruct (G.AcyclicSCC (k, v)) r
    = let v' = S.foldr (\k r' -> fromMaybe (error "reconstruct (AcyclicSCC)") (M.lookup k r) `S.union` r') v v
       in M.insert k v' r
reconstruct (G.CyclicSCC  kvs   ) r
    = let v  = S.unions (map snd kvs)
          v' = S.foldr (\k r' -> fromMaybe (error "reconstruct (CyclicSCC)") (M.lookup k r) `S.union` r') v v
       in foldr (\(k, _) -> M.insert k v') r kvs

-- | Logging

message :: String -> State (s, [String]) ()
message m = do (s, ms) <- get
               put (s, m:ms)
               return ()

-- | Fresh identifiers

class Fresh a where 
    fresh :: State ([Name], s') a
    
instance Fresh Name where
    fresh = do (x:xs, s') <- get
               put (xs, s')
               return x
               
instance (Fresh a, Fresh b) => Fresh (a, b) where
    fresh = do x <- fresh
               y <- fresh
               return (x, y)
               
instance (Fresh a, Fresh b, Fresh c) => Fresh (a, b, c) where
    fresh = do x <- fresh
               y <- fresh
               z <- fresh
               return (x, y, z)
               
instance Fresh Ty where
    fresh = do a <- fresh
               return (TyVar a)
               
instance Fresh TyScheme where
    fresh = do t <- fresh
               return (Forall [] [] S.empty t)

instance Fresh Be where
    fresh = do b <- fresh
               return (BeUnif b)

freshIdents = map (\n -> "_{" ++ show n ++ "}") [1..]

-- | Free variables

class FV t where
    ftv, fbv, fv :: t -> S.Set Ident
    fv x = ftv x `S.union` fbv x

instance FV Ty where
    ftv (TyVar a)       = S.singleton a
    ftv TyUnit          = S.empty
    ftv TyInt           = S.empty
    ftv TyBool          = S.empty
    ftv (TyPair t1 t2)  = ftv t1 `S.union` ftv t2
    ftv (TyList t)      = ftv t
    ftv (TyFun t1 b t2) = ftv t1 `S.union` ftv b `S.union` ftv t2
    ftv (TyChan t)      = ftv t
    ftv (TyCom t b)     = ftv t `S.union` ftv b
    
    fbv (TyVar a)       = S.empty
    fbv TyUnit          = S.empty
    fbv TyInt           = S.empty
    fbv TyBool          = S.empty
    fbv (TyPair t1 t2)  = fbv t1 `S.union` fbv t2
    fbv (TyList t)      = fbv t
    fbv (TyFun t1 b t2) = fbv t1 `S.union` fbv b `S.union` fbv t2
    fbv (TyChan t)      = fbv t
    fbv (TyCom t b)     = fbv t `S.union` fbv b

instance FV Be' where
    ftv (BeVar  _) = S.empty
    ftv (BeChan t) = ftv t

    fbv (BeVar  b) = S.singleton b
    fbv (BeChan t) = fbv t

instance FV Be where
    ftv (BeUnif u ) = S.empty
    ftv (Be     bs) = unionMap ftv bs

    fbv (BeUnif u ) = S.singleton u
    fbv (Be     bs) = unionMap fbv bs

instance FV TyScheme where
    ftv (Forall as bs cs t) = (ftv cs `S.union` ftv t) `S.difference` (S.fromList as)
    fbv (Forall as bs cs t) = (fbv cs `S.union` fbv t) `S.difference` (S.fromList bs)

instance FV TyEnv where
    ftv = S.unions . M.elems . M.map ftv
    fbv = S.unions . M.elems . M.map fbv

instance FV Constr' where
    ftv (t1 :<:  t2) = ftv t1 `S.union` ftv t2
    ftv (b1 :<*: b2) = ftv b1 `S.union` ftv b2
    
    fbv (t1 :<:  t2) = fbv t1 `S.union` fbv t2
    fbv (b1 :<*: b2) = fbv b1 `S.union` fbv b2

instance FV Constr where
    ftv = unionMap ftv
    fbv = unionMap fbv
    
-- | Substitutions

infixr 0 $@
infixr 5 $+
infixr 9 $.

data Subst = Subst (M.Map Ident Ty) (M.Map Ident Ident) deriving Show

idSubst :: Subst
idSubst = Subst M.empty M.empty

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $@ s1) $+ s2

($+) :: Subst -> Subst -> Subst
($+) (Subst tv1 bv1) (Subst tv2 bv2)
    = Subst (M.unionWith (error "domains not distinct") tv1 tv2)
            (M.unionWith (error "domains not distinct") bv1 bv2)

class Substitute t where
    ($@) :: Subst -> t -> t
    
instance Substitute Ident where
    Subst _ bv $@ u | Just u' <- M.lookup u bv = u'
                    | otherwise                = u

instance Substitute Subst where
    subst $@ (Subst tv bv)
        = Subst (M.map (subst $@) tv) (M.map (subst $@) bv)
     
instance Substitute Ty where -- FIXME: incomplete
    Subst tv _ $@ t@(TyVar a)    | Just t' <- M.lookup a tv = t'
                                 | otherwise                = t
    _          $@ TyUnit         = TyUnit
    _          $@ TyInt          = TyInt
    _          $@ TyBool         = TyBool
    subst      $@ (TyPair t1 t2) = TyPair (subst $@ t1) (subst $@ t2)
    subst      $@ (TyList t)     = TyList (subst $@ t)
    subst      $@ (TyFun t b t') = TyFun (subst $@ t) (subst $@ b) (subst $@ t')
    subst      $@ (TyChan t)     = TyChan (subst $@ t)
    subst      $@ (TyCom t b)    = TyCom (subst $@ t) (subst $@ b)
    
instance Substitute Be' where
    Subst _ bv $@ (BeVar b)  | Just b' <- M.lookup b bv = BeVar b'
                             | otherwise                = BeVar b
    subst      $@ (BeChan t) = BeChan (subst $@ t)

instance Substitute Be where
    subst $@ (BeUnif u ) = BeUnif (subst $@ u)
    subst $@ (Be     bs) = Be (S.map (subst $@) bs)
    
instance Substitute Constr' where
    subst $@ (t1 :<:  t2) = (subst $@ t1) :<:  (subst $@ t2)
    subst $@ (b1 :<*: b2) = (subst $@ b1) :<*: (subst $@ b2)

instance Substitute Constr where
    subst $@ cs = S.map (subst $@) cs
    
instance Substitute TyScheme where
    Subst tv bv $@ (Forall as bs c t)
        = let s' = Subst (tv `restrict` as) (bv `restrict` bs)
           in Forall as bs (s' $@ c) (s' $@ t)
    
instance Substitute TyEnv where
    subst $@ env = M.map (subst $@) env
    
-- | Miscellaneous

restrict :: Ord k => M.Map k a -> [k] -> M.Map k a
restrict = foldr M.delete

unionMap :: (Ord a, Ord b) => (a -> S.Set b) -> S.Set a -> S.Set b
unionMap f = S.unions . S.toList . S.map f

-- | Testing

transGraph1 = M.fromList [("a", S.singleton "b"), ("b", S.singleton "c"), ("c", S.singleton "d"), ("d", S.empty)]
transGraph2 = M.fromList [("a",S.singleton "b"), ("b", S.singleton "c"), ("c", S.singleton "d"), ("d", S.fromList ["b", "e"]), ("e", S.singleton "f"), ("f", S.empty)]
