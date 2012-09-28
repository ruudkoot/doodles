{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}

module Main where

-- PERFORMANCE: commutativity and associativity of S.union (bigset `S.union` smallset)

import Control.Monad
import Control.Monad.State

import qualified Data.Graph as G
import qualified Data.List  as L
import qualified Data.Map   as M
import           Data.Maybe
import qualified Data.Set   as S
import qualified Data.Tree  as T

import qualified Data.UnionFind.IntMap as UF    -- union-find-0.2

-- deriving instance Ord a => Ord (UF.Point a)

main = undefined

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
         (s2, c2) <- return (s1, c1) -- force c1
         (c3, t3, b3) <- return (c2, t1, b1) -- reduce
         return (s2 $. s1, t3, b3, c3)

infer' :: TyEnv -> Expr -> State ([Name], ()) (Subst, Ty, Be, Constr)
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

force :: Constr -> (Subst, Constr)
force c = let (s', c', equiv') = rewrite (idSubst, c, eqc)
           in if atomic c' then (s', c') else error "forcing failed"

rewrite = undefined
eqc = undefined
atomic = undefined

{-
mrml :: Constr' -> ???
mrml (t :<: TyVar a) = Just ???
mrml (TyVar a :<: t) = Just ???
mrml _               = Nothing
-}

type Equiv = (M.Map Name (UF.Point Name), UF.PointSupply Name)

(??) :: Equiv -> Name -> UF.Point Name
(pm, _) ?? n = fromJust (M.lookup n pm)

m' :: Constr -> State ([Name], ()) ()
m' c = do let univ     = fv c
          let (pm, pa) = S.foldr (\a' (m, ps) -> let (ps', p) = UF.fresh ps a'
                                                  in (M.insert a' p m, ps'))
                                 (M.empty, UF.newPointSupply)
                                 univ
          return undefined
          
m :: Name -> Ty -> Equiv -> State ([Name], ()) (Maybe (Subst, Equiv))
m a t equiv
    = do let as         = filter (UF.equivalent (snd equiv) (equiv ?? a))
                                 (map (equiv ??) (M.keys (fst equiv)))
         let n          = length as
         let (as0, bs0) = shGet t
         let m          = length as0
         ass            <- replicateM n (replicateM         m      fresh)
         bss            <- replicateM n (replicateM (length (bs0)) fresh)
         let r          = Subst (M.fromList (zipWith3 (\a as bs -> (UF.descriptor (snd equiv) a, shPut t (as, bs))) as ass bss)) M.empty
         let equiv'     = undefined
         return (Just (r, equiv'))
          
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
shPut' (TyVar _) (a:as, bs) = (TyVar a, as, bs)
shPut' TyUnit    (  as, bs) = (TyUnit , as, bs)
shPut' TyBool    (  as, bs) = (TyBool , as, bs)
shPut' TyInt     (  as, bs) = (TyInt  , as, bs)
shPut' (TyPair t1 t2) (as0, bs0) = let (t1', as1, bs1) = shPut' t1 (as0, bs0)
                                       (t2', as2, bs2) = shPut' t2 (as1, bs1)
                                    in (TyPair t1' t2', as2, bs2)
shPut' (TyFun t1 b t2) (as0, bs0) = let (t1', as1, b':bs1) = shPut' t1 (as0, bs0)
                                        (t2', as2,    bs2) = shPut' t2 (as1, bs2)
                                     in (TyFun t1' b' t2', as2, bs2)
shPut' (TyList t) (as, bs) = let (t', as', bs') = shPut' t (as, bs)
                              in (TyList t', as', bs')
shPut' (TyChan t) (as, bs) = let (t', as', bs') = shPut' t (as, bs)
                              in (TyChan t', as', bs')
shPut' (TyCom t b) (as, bs) = let (t', as', b':bs') = shPut' t (as, bs)
                               in (TyCom t' b', as', bs')


(+++) :: ([a], [b]) -> ([a], [b]) -> ([a], [b])
(xs1, ys1) +++ (xs2, ys2) = (xs1 ++ xs2, ys1 ++ ys2)

rewriteC c
    = process rewriteC'


process :: Ord a => (a -> Maybe (S.Set a)) -> S.Set a -> S.Set a
process f = process' S.empty
    where process' u w
            = case S.minView w of
                    Nothing       -> u
                    Just (c', w') -> case f c' of
                                        Nothing  -> process' (c' `S.insert` u) w'
                                        Just w'' -> process' u (w' `S.union` w'')

rewriteC' :: Constr' -> Maybe Constr
rewriteC' (Be bs :<*: b)  -- \emptyset and \cup
    = Just $ S.map (\b' -> (Be (S.singleton b') :<*: b)) bs
rewriteC' (TyUnit :<: TyUnit)
    = Just $ S.empty
rewriteC' (TyBool :<: TyBool)
    = Just $ S.empty
rewriteC' (TyInt :<: TyInt)
    = Just $ S.empty
rewriteC' (TyPair t1 t2 :<: TyPair t3 t4)
    = Just $ S.fromList [t1 :<: t3, t2 :<: t4]
rewriteC' (TyList t1 :<: TyList t2)
    = Just $ S.fromList [t1 :<: t2]
rewriteC' (TyChan t1 :<: TyChan t2)
    = Just $ S.fromList [t1 :<: t2, t2 :<: t1]
rewriteC' (TyCom  t1 b1 :<: TyCom  t2 b2)
    = Just $ S.fromList [t1 :<: t2, b1 :<*: b2]
rewriteC' (TyFun t1 b1 t2 :<: TyFun t3 b2 t4)
    = Just $ S.fromList [t3 :<: t1, b1 :<*: b2, t2 :<: t4]
rewriteC' _
    = Nothing

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
    = let f0 = S.foldr
                (\(g1 :<: g2) r ->
                    S.foldr (\x -> M.insertWith S.union x (fv g1)) r (fv g2))
                M.empty c
          fc = transitiveClosure (reflexiveClosure f0)
       in S.filter (\k -> not (S.null (fromJust (M.lookup k fc) `S.intersection` x))) (M.keysSet fc)
       
downClose x c
    = let f0 = S.foldr
                (\(g1 :<: g2) r ->
                    S.foldr (\x -> M.insertWith S.union x (fv g2)) r (fv g1))
                M.empty c
          fc = transitiveClosure (reflexiveClosure f0)
       in S.filter (\k -> not (S.null (fromJust (M.lookup k fc) `S.intersection` x))) (M.keysSet fc)

biClose x c
    = let f0 = S.foldr
                (\(g1 :<: g2) r ->
                    S.foldr (\x -> M.insertWith S.union x (fv g2)) r (fv g1))
                M.empty c
          fc = transitiveClosure (symmetricClosure (reflexiveClosure f0))
       in S.filter (\k -> not (S.null (fromJust (M.lookup k fc) `S.intersection` x))) (M.keysSet fc)

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
    = let v' = S.foldr (\k r' -> fromJust (M.lookup k r) `S.union` r') v v
       in M.insert k v' r
reconstruct (G.CyclicSCC  kvs   ) r
    = let v  = S.unions (map snd kvs)
          v' = S.foldr (\k r' -> fromJust (M.lookup k r) `S.union` r') v v
       in foldr (\(k, _) -> M.insert k v') r kvs

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
    ftv :: t -> S.Set Ident
    fbv :: t -> S.Set Ident
    fv :: t -> S.Set Ident
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
    ftv (BeVar _) = S.empty

instance FV Be where
    ftv (BeUnif u) = S.empty
    ftv (Be bs)    = unionMap ftv bs
    
instance FV TyEnv where

instance FV Constr where
    
-- | Substitutions

infixr 0 $@
infixr 9 $.

data Subst = Subst (M.Map Ident Ty) (M.Map Ident Ident)

idSubst :: Subst
idSubst = Subst M.empty M.empty

($.) :: Subst -> Subst -> Subst
s2 $. s1 = (s2 $@ s1) `substUnion` s2
    where 
        substUnion (Subst tv1 bv1) (Subst tv2 bv2)
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
    Subst tv _ $@ (TyVar a)      | Just t <- M.lookup a tv = t
    subst      $@ (TyFun t b t') = TyFun (subst $@ t) (subst $@ b) (subst $@ t')
    _          $@ x              = x

instance Substitute Be' where
    Subst _ bv $@ (BeVar b) | Just b' <- M.lookup b bv = BeVar b'
    _          $@ x         = x

instance Substitute Be where
    subst $@ (BeUnif u) = BeUnif (subst $@ u)
    
instance Substitute Constr' where

instance Substitute Constr where
    
instance Substitute TyScheme where
    Subst tv bv $@ (Forall as bs c t)
        = let s' = Subst (tv `restrict` as) (bv `restrict` bs)
           in Forall as bs (s' $@ c) (s' $@ t)
    
instance Substitute TyEnv where
    subst $@ env = M.map (\t -> subst $@ t) env
    
-- | Miscellaneous

restrict :: Ord k => M.Map k a -> [k] -> M.Map k a
restrict = foldr M.delete

unionMap :: (Ord a, Ord b) => (a -> S.Set b) -> S.Set a -> S.Set b
unionMap f = S.unions . S.toList . S.map f

-- | Testing

transGraph1 = M.fromList [("a", S.singleton "b"), ("b", S.singleton "c"), ("c", S.singleton "d"), ("d", S.empty)]
transGraph2 = M.fromList [("a",S.singleton "b"), ("b", S.singleton "c"), ("c", S.singleton "d"), ("d", S.fromList ["b", "e"]), ("e", S.singleton "f"), ("f", S.empty)]
