{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Main (main) where

-- PERFORMANCE: commutativity and associativity of S.union (bigset `S.union` smallset)
--              M.findWithDefault
--              TyScheme, quantified variables as list or set?

import           Prelude                hiding (cycle)

import           Control.Monad
import           Control.Monad.Identity
import           Control.Monad.State

import qualified Data.Graph             as G
import qualified Data.List              as L
import qualified Data.Map               as M
import           Data.Maybe
import qualified Data.Set               as S
import qualified Data.Tree              as T
import qualified Data.Tree.Zipper       as Z               -- == rose-zipper-0.2

import qualified Equiv                  as E               -- => union-find-0.2

-- | Main

main = do let expr = exC
          let init = (freshIdents, Z.fromTree emptyInferenceTree, [])
          let ((s, t, b, c), (_, tree, msgs)) = runState (infer M.empty expr) init
          putStrLn $ "== MESSAGES ============================================="
          putStr   $ unlines msgs
          putStrLn $ "== RESULTS =============================================="
          putStrLn $ "Type        : " ++ show t
          putStrLn $ "Behaviour   : " ++ show b
          putStrLn $ "Constraints : " ++ show c
          putStrLn $ "Substitution: " ++ show s
          putStrLn $ "== INFERENCE TREE ======================================="
          putStrLn $ T.drawTree (fmap show (Z.toTree tree))

-- * Examples
          
exA = Let "id" (Fn "x" (Var "x")) (Var "id")
exB = Let "id" (Fn "x" (Var "x")) (Var "id" `App` Con (Bool True))
exC = Let "id" (Fn "x" (Var "x")) (Var "id" `App` Var "id") -- DOES NOT TYPECHECK
exD = Con (Bool True)
exE = Con (Int 42)
exF = Fn "x" (Con (Bool True))
exG = Fn "x" (Var "x")
exH = Fn "x" (Var "x") `App` (Con (Bool True))
exI = (Fn "x" (Var "x")) `App` (Fn "y" (Var "y"))
          
ex230 = Fn "f" (Let "id" (Fn "y" (
                           (If (Con (Bool True))
                               (Var "f")
                               (Fn "x" ((Con Sync `App` (Con Send `App`
                                            _pair (Con Channel `App` Con Unit)
                                                  (Var "y"))) `_seq`
                                       (Var "x")))) `_seq`
                           (Var "y")))
                    (Var "id" `App` Var "id"))

_seq :: Expr -> Expr -> Expr
_seq e1 e2 = Con Snd `App` (Con Pair `App` e1 `App` e2)

_pair :: Expr -> Expr -> Expr
_pair e1 e2 = Con Pair `App` e1 `App` e2

-- * Testing

transGraph1 = M.fromList [("a", S.singleton "b"), ("b", S.singleton "c"), ("c", S.singleton "d"), ("d", S.empty)]
transGraph2 = M.fromList [("a",S.singleton "b"), ("b", S.singleton "c"), ("c", S.singleton "d"), ("d", S.fromList ["b", "e"]), ("e", S.singleton "f"), ("f", S.empty)]

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

-- * Monad

type MyMonad r = State ([Name], InferenceTree Rule, [String]) r

-- * Inference

infer :: TyEnv -> Expr -> MyMonad (Subst, Ty, Be, Constr)
infer env e
    = do down
         (s1, t1, b1, c1) <- infer' env e
         (s2,         c2) <- force env c1
         Identity (c3, t3, b3) <- reduce (s2 $@ s1 $@ env) c2 (s2 $@ t1) (s2 $@ b1)
         up
         putRule (W c1 c2 s2)
         return (s2 $. s1, t3, b3, c3)

infer' :: TyEnv -> Expr -> MyMonad (Subst, Ty, Be, Constr)
infer' env e@(Con c)
    = do (s, t, b, c) <- inst (typeOf c)
         t' <- mkSimple t
         putRule (W' env e t' b c s)
         return (s, t', b, c)
infer' env e@(Var x)
    | Just ts <- M.lookup x env = do (s, t, b, c) <- inst ts
                                     putRule (W' env e t b c s)
                                     return (s, t, b, c)
    | otherwise                 = error $ "variable '" ++ x ++ "' not in scope " ++ show env
infer' env e@(Fn x e0)
    = do down
         a <- fresh
         (s0, t0, b0, c0) <- infer (M.insert x (injTS a) env) e0
         b <- fresh
         up
         putRule (W' env e (TyFun (s0 $@ a) b t0) (Be S.empty) (c0 `S.union` S.fromList [b0 :<*: b]) s0)
         return ( s0, TyFun (s0 $@ a) b t0, Be S.empty
                , c0 `S.union` S.fromList [b0 :<*: b] )
infer' env e@(App e1 e2)
    = do down
         (s1, t1, b1, c1) <- infer env e1
         (s2, t2, b2, c2) <- infer (s1 $@ env) e2
         (a, b) <- fresh
         up
         putRule (W' env e a (s2 $@ b1) (s2 $@ c1 `S.union` c2 `S.union` S.fromList [s2 $@ t1 :<: TyFun t2 b a]) (s2 $. s1))
         return ( s2 $. s1, a, s2 $@ b1 `joinBe` b2 `joinBe` injBe b
                , s2 $@ c1 `S.union` c2
                           `S.union` S.fromList [s2 $@ t1 :<: TyFun t2 b a] )
infer' env e@(Let x e1 e2)
    = do down
         (s1, t1, b1, c1) <- infer env e1
         let ts1 = gen (s1 $@ env) b1 c1 t1
         (s2, t2, b2, c2) <- infer (M.insert x ts1 (s1 $@ env)) e2
         up
         putRule (W' env e t2 (s2 $@ b1) (s2 $@ c2 `S.union` c1) (s2 $. s1))
         return ( s2 $. s1, t2, s2 $@ b1 `joinBe` b2, s2 $@ c2 `S.union` c1 )
infer' env e@(Rec f x e0)
    | f == x = error "binders not distinct"
    | otherwise
        = do down
             (a1, b, a2) <- fresh
             (s0, t0, b0, c0) <- infer (M.insert x (injTS a1)
                                            (M.insert f (injTS (TyFun a1 b a2)) env)) e0
             up
             putRule (W' env e (s0 $@ TyFun a1 b a2) (Be S.empty) (c0 `S.union` S.fromList [b0 :<*: (s0 $@ b), t0 :<: (s0 $@ a2)]) s0)
             return ( s0, s0 $@ TyFun a1 b a2, Be S.empty
                    , c0 `S.union` S.fromList [b0 :<*: (s0 $@ b), t0 :<: (s0 $@ a2)] )
infer' env e@(If e0 e1 e2)
    = do down
         (s0, t0, b0, c0) <- infer env e0
         (s1, t1, b1, c1) <- infer (s0 $@ env) e1
         (s2, t2, b2, c2) <- infer (s1 $@ s0 $@ env) e2
         a <- fresh
         up
         putRule (W' env e a (s2 $@ s1 $@ b0 `joinBe` (s2 $@ b1) `joinBe` b2) (s2 $@ s1 $@ c0 `S.union` (s2 $@ c1) `S.union` c2 `S.union` S.fromList [s2 $@ s1 $@ t0 :<: TyBool, s2 $@ t1 :<: a, t2 :<: a]) (s2 $. s1 $. s0))
         return ( s2 $. s1 $. s0, a, s2 $@ s1 $@ b0 `joinBe` (s2 $@ b1) `joinBe` b2
                , s2 $@ s1 $@ c0 `S.union` (s2 $@ c1) `S.union` c2 `S.union`
                    S.fromList [s2 $@ s1 $@ t0 :<: TyBool, s2 $@ t1 :<: a, t2 :<: a] )

-- * Forcing (decompostion and matching)

force :: TyEnv -> Constr -> MyMonad (Subst, Constr)
force env c -- FIXME: env only needed to print error message
    = do message "|Forcing|"
         (s', c', _) <- rewrite (idSubst, c, eqc c)
         if atomic c'
            then return (s', c')
            else error $ "forcing failed: " ++ show c' ++ show env
                
eqc :: Constr -> E.Equiv Name
eqc = S.foldr E.insert E.empty . ftv

atomic :: Constr -> Bool -- FIXME: is this strict/lenient enough?
atomic = and . map atomic' . S.toList
    where atomic' (TyVar  _ :<:  TyVar  _) = True
          atomic' (Be chan  :<*: BeUnif _) | [BeChan _] <- S.toList chan = True
          atomic' (Be var   :<*: BeUnif _) | [BeVar  _] <- S.toList var  = True -- FIXME: promote?
          atomic' (BeUnif _ :<*: BeUnif _) = True
          atomic' _                        = False

rewrite :: (Subst, Constr, E.Equiv Name) -> MyMonad (Subst, Constr, E.Equiv Name)
rewrite (s, c, eq)
    = do dc <- process decompose c
         when (c /= dc) $
            do message $ "Decompose: " ++ show c
               message $ "        ~> " ++ show dc
         message $ "Match    : " ++ show dc
         message $ "           w/ " ++ show s
         message $ "         & w/ " ++ show eq
         maybeMatch <- process2 (s, dc, eq)
         case maybeMatch of
            Nothing             -> return (s, dc, eq)
            Just (s', dc', eq') -> do message $ "        ~> " ++ show dc'
                                      message $ "           w/ " ++ show s'
                                      message $ "         & w/ " ++ show eq'
                                      rewrite (s', dc', eq')
         

process :: (Ord a, Show a) => (a -> Maybe (S.Set a)) -> S.Set a -> MyMonad (S.Set a)
process f x = process' S.empty x
    where process' u w
            = do case S.minView w of
                   Nothing       -> return u
                   Just (c', w') -> case f c' of
                                       Nothing  -> process' (c' `S.insert` u) w'
                                       Just w'' -> process' u (w' `S.union` w'')

decompose :: Constr' -> Maybe Constr
decompose (Be bs :<*: b)  -- \emptyset and \cup + custom promotion rule
    | S.size bs /= 1 = Just $ S.map (\b' -> (Be (S.singleton b') :<*: b)) bs
--  | S.size bs == 1, Just (BeVar b', _) <- S.minView bs = Just $ S.singleton (BeUnif b' :<*: b)
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

process2 :: (Subst, Constr, E.Equiv Name) ->
                MyMonad (Maybe (Subst, Constr, E.Equiv Name))
process2 = process' S.empty
    where process' u (s, w, eq)
            = do case S.minView w of
                   Nothing       -> return Nothing
                   Just (c', w') ->
                        do maybeSCE <- mrml (s, u `S.union` w', eq) c'
                           case maybeSCE of 
                                Nothing -> process' (c' `S.insert` u) (s, w', eq)
                                result  -> return result

mrml :: (Subst, Constr, E.Equiv Name) -> Constr' ->
            MyMonad (Maybe (Subst, Constr, E.Equiv Name))
mrml (s, c, equiv) (t :<: TyVar a)
    = do maybeSE <- m a t equiv
         case maybeSE of
            Nothing          -> 
                return $ Nothing
            Just (r, equiv') ->
                return $ Just ( r $. s
                              , S.insert ((r $@ t) :<: (r $@ (TyVar a))) (r $@ c)
                              , equiv' )
mrml (s, c, equiv) (TyVar a :<: t)
    = do maybeSE <- m a t equiv
         case maybeSE of
            Nothing          ->
                return $ Nothing
            Just (r, equiv') ->
                return $ Just ( r $. s
                              , S.insert ((r $@ (TyVar a)) :<: (r $@ t)) (r $@ c)
                              , equiv' )
mrml _             _
    = return Nothing

m :: Name -> Ty -> E.Equiv Name ->
        MyMonad (Maybe (Subst, E.Equiv Name))
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
         let equiv' = foldr (uncurry E.insert2) E.empty $
                        [(a', a'') | (a',a'') <- E.elems equiv
                                   , a' `S.notMember` as && a'' `S.notMember` as]
                            ++
                        concatMap (uncurry zip) [(as0,as') | as' <- ass]
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
                                        (t2', as2,    bs2) = shPut' t2 (as1, bs1)
                                     in (TyFun t1' b' t2', as2, bs2)
shPut' (TyList t)      (as, bs)   = let (t', as', bs') = shPut' t (as, bs)
                                     in (TyList t', as', bs')
shPut' (TyChan t)      (as, bs)   = let (t', as', bs') = shPut' t (as, bs)
                                     in (TyChan t', as', bs')
shPut' (TyCom t b)     (as, bs)   = let (t', as', b':bs') = shPut' t (as, bs)
                                     in (TyCom t' b', as', bs')

(+++) :: ([a], [b]) -> ([a], [b]) -> ([a], [b])
(xs1, ys1) +++ (xs2, ys2) = (xs1 ++ xs2, ys1 ++ ys2)

-- * Reduction

type Always = Identity

type ReductionRule succeeds
    = TyEnv -> Constr -> Ty -> Be -> MyMonad (succeeds (Constr, Ty, Be))

doNotReduce :: ReductionRule Always
doNotReduce _ c t b = return $ Identity (c, t, b)

reduce :: ReductionRule Always
reduce env c t b
    = do c' <- processRedund redund c
         maybeCTB <- reduceAll [ processCycle  cycle
                               , processTrans  shrink
                               , processTrans  boost  ]
                               env c' t b
         case maybeCTB of
            Nothing            -> return $ Identity (c', t, b)
            Just (c'', t', b') -> reduce env c'' t' b'

reduceAll :: [ReductionRule Maybe] -> ReductionRule Maybe
reduceAll []     env c t b = return Nothing
reduceAll (p:ps) env c t b = do maybeCTB <- p env c t b
                                case maybeCTB of
                                    Nothing -> reduceAll ps env c t b
                                    justCTB -> return justCTB

processRedund :: (Constr -> Constr' -> Bool) -> Constr -> MyMonad (Constr)
processRedund f c = process' S.empty c
    where process' u w
            = do case S.minView w of
                   Nothing       -> return u
                   Just (c', w') -> if f (u `S.union` w') c'
                                    then process'                u  w'
                                    else process' (c' `S.insert` u) w'

processCycle :: ReductionRule Maybe -> ReductionRule Maybe
processCycle = id

processTrans :: (Constr' -> ReductionRule Maybe) -> ReductionRule Maybe
processTrans f env c t b = process' S.empty c
    where process' u w
            = do case S.minView w of
                    Nothing -> return Nothing
                    Just (c', w') -> do maybeCTB <- f c' env (u `S.union` w') t b
                                        case maybeCTB of
                                            Nothing -> process' (c' `S.insert` u) w'
                                            justCTB -> return justCTB

redund :: Constr -> Constr' -> Bool
redund c (TyVar  g' :<:  TyVar  g)
    | reachable c g' g = True
redund c (BeUnif g' :<*: BeUnif g)
    | reachable c g' g = True
redund _ _
    = False

cycle :: ReductionRule Maybe
cycle env c t b
    | ((g, g'):_) <- [(g, g') | g <- S.toList (fv c), g' <- S.toList (fv c)
    , g /= g', g `S.notMember` fv env, reachable c g g', reachable c g' g]
    = let s = evilSubst g g' in return $ Just (s $@ c, s $@ t, s $@ b)
cycle _ _ _ _
    = return Nothing

shrink :: Constr' -> ReductionRule Maybe
shrink (TyVar  g' :<:  TyVar  g) env c t b
    | g' /= g, g `S.notMember` fv env, g `S.notMember` fv (rhs c), monotonic
    = let s = evilSubst g g' in return $ Just (s $@ c, s $@ t, s $@ b)
        where monotonic = let (lht, lhb) = lhs c
                           in and (map (`isMonotonicIn` g) (t : S.toList lht))
                              && and (map (`isMonotonicIn` g) (b : S.toList lhb))
shrink (BeUnif g' :<*: BeUnif g) env c t b
    | g' /= g, g `S.notMember` fv env, g `S.notMember` fv (rhs c), monotonic
    = let s = evilSubst g g' in return $ Just (s $@ c, s $@ t, s $@ b)
        where monotonic = let (lht, lhb) = lhs c
                           in and (map (`isMonotonicIn` g) (t : S.toList lht))
                              && and (map (`isMonotonicIn` g) (b : S.toList lhb))
shrink _ _ _ _ _
    = return Nothing
                              
boost :: Constr' -> ReductionRule Maybe
boost (TyVar  g :<:  TyVar  g') env c t b
    | g' /= g, g `S.notMember` fv env, antimonotonic
    = let s = evilSubst g g' in return $ Just (s $@ c, s $@ t, s $@ b)
        where antimonotonic = let (lht, lhb) = lhs c
                               in and (map (`isAntimonotonicIn` g) (t : S.toList lht))
                                  && and (map (`isAntimonotonicIn` g) (b : S.toList lhb))
boost (BeUnif g :<*: BeUnif g') env c t b
    | g' /= g, g `S.notMember` fv env, antimonotonic
    = let s = evilSubst g g' in return $ Just (s $@ c, s $@ t, s $@ b)
        where antimonotonic = let (lht, lhb) = lhs c
                               in and (map (`isAntimonotonicIn` g) (t : S.toList lht))
                                  && and (map (`isAntimonotonicIn` g) (b : S.toList lhb))
boost _ _ _ _ _
    = return Nothing

lhs :: Constr -> (S.Set Ty, S.Set Be)
lhs = S.foldr lhs' (S.empty, S.empty)
    where lhs' (t :<:  _) (ts, bs) = (S.insert t ts, bs)
          lhs' (b :<*: _) (ts, bs) = (ts, S.insert b bs)

rhs :: Constr -> (S.Set Ty, S.Set Be)
rhs = S.foldr rhs' (S.empty, S.empty)
    where rhs' (_ :<:  t) (ts, bs) = (S.insert t ts, bs)
          rhs' (_ :<*: b) (ts, bs) = (ts, S.insert b bs)
          
evilSubst :: Name -> Name -> Subst {- FIXME: this substitution is an evil hack -}
evilSubst g g' = Subst (M.singleton g (TyVar g')) (M.singleton g g')

-- PERFORMANCE: completely recalculating this every time will be quite expensive
-- is there a data structure for online RT/reachability computation?
--    * www.cs.tau.ac.il/~zwick/slides/dynamic-uri.ppt (decremental reachability)
-- alternatively, use a (shortest) path algorithm
reachable :: Constr -> Name -> Name -> Bool
reachable c y y'
    = let m0 = S.foldr (\g -> M.insert g (S.singleton g)) M.empty (fv c)
          f0 = S.foldr reachabilityHelper m0 c
          fc = transitiveClosure (reflexiveClosure f0)  -- reflexivity?
       in S.member y (M.findWithDefault S.empty y' fc)

reachabilityHelper :: Constr' -> M.Map Name (S.Set Name) -> M.Map Name (S.Set Name)
-- PERFORMANCE: Change S.union to S.insert/S.singleton depending on existence
reachabilityHelper (TyVar  g1 :<:  TyVar  g2) m
    = M.insertWith S.union g2 (S.singleton g1) m
reachabilityHelper (BeUnif g1 :<*: BeUnif g2) m
    = M.insertWith S.union g2 (S.singleton g1) m
reachabilityHelper (Be bs :<*: BeUnif g2) m
    | S.size bs == 1, Just (BeVar g1, _) <- S.minView bs
        = M.insertWith S.union g2 (S.singleton g1) m
    | S.size bs == 1, Just (BeChan _, _) <- S.minView bs
        = m
reachabilityHelper x                    _ = error $ show x

-- * Monotonicity

class Monotonicity a where
    na :: a -> S.Set Name
    nm :: a -> S.Set Name
    
instance Monotonicity Ty where
    na (TyVar a)        = S.singleton a
    na  TyUnit          = S.empty
    na  TyInt           = S.empty
    na  TyBool          = S.empty
    na (TyFun  t1 b t2) = nm t1 `S.union` na b `S.union` na t2
    na (TyPair t1   t2) = na t1 `S.union` na t2
    na (TyList t      ) = na t
    na (TyChan t      ) = fv t
    na (TyCom  t  b   ) = na t `S.union` na b
    
    nm (TyVar a)        = S.empty
    nm  TyUnit          = S.empty
    nm  TyInt           = S.empty
    nm  TyBool          = S.empty
    nm (TyFun  t1 b t2) = na t1 `S.union` nm b `S.union` nm t2
    nm (TyPair t1   t2) = nm t1 `S.union` nm t2
    nm (TyList t      ) = nm t
    nm (TyChan t      ) = fv t
    nm (TyCom  t  b   ) = nm t `S.union` nm b


instance Monotonicity Be' where
    na (BeVar  b) = S.singleton b
    na (BeChan t) = fv t
    
    nm (BeVar  b) = S.empty
    nm (BeChan t) = fv t

instance Monotonicity Be where
    na (BeUnif b ) = S.singleton b
    na (Be     bs) = unionMap na bs
    
    nm (BeUnif b ) = S.empty
    nm (Be     bs) = unionMap na bs
    
isMonotonicIn :: Monotonicity g => g -> Name -> Bool
isMonotonicIn g y = y `S.notMember` nm g

isAntimonotonicIn :: Monotonicity g => g -> Name -> Bool
isAntimonotonicIn g y = y `S.notMember` na g

-- * Primitive types

typeOf :: Con -> TyScheme
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
typeOf Nil
    = Forall ["a"] [] S.empty
        (TyList (TyVar "a"))
typeOf Cons
    = Forall ["a"] [] S.empty
        (TyFun (TyVar "a")
               (Be S.empty)
               (TyFun (TyList (TyVar "a")) (Be S.empty) (TyList (TyVar "a"))))
typeOf Hd
    = Forall ["a"] [] S.empty
        (TyFun (TyList (TyVar "a")) (Be S.empty) (TyVar "a"))
typeOf Tl
    = Forall ["a"] [] S.empty
        (TyFun (TyList (TyVar "a")) (Be S.empty) (TyList (TyVar "a")))
typeOf IsNil
    = Forall ["a"] [] S.empty
        (TyFun (TyList (TyVar "a")) (Be S.empty) TyBool)
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

mkSimple :: Ty -> MyMonad Ty
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

mkSimple' :: Be -> MyMonad Be
mkSimple' b@(BeUnif _)        = return b
mkSimple' (Be bs) | S.null bs = fresh
                  | otherwise = error "type not simplifiable"

-- * Instantiation

inst :: TyScheme -> MyMonad (Subst, Ty, Be, Constr)
inst (Forall as bs c t)
    = do as' <- replicateM (length as) fresh
         bs' <- replicateM (length bs) fresh
         let r = Subst (M.fromList (zipWith (\a a' -> (a, TyVar a')) as as'))
                       (M.fromList (zip                              bs bs'))
         return (idSubst, r $@ t, Be S.empty, r $@ c)

-- * Generalization
         
gen env b c t
    = let abs = (fv t {-`biClose` c) `S.difference` ((fv env `S.union` fv b) `downClose` c-})
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

transitiveClosure :: (Ord a, Show a) => M.Map a (S.Set a) -> M.Map a (S.Set a)
transitiveClosure m
    = foldr reconstruct m . reverse . G.stronglyConnComp . toEdgeList $ m

toEdgeList :: M.Map k (S.Set a) -> [((k, S.Set a), k, [a])]
toEdgeList
    = M.foldrWithKey (\k v -> (:) ((k, v), k, S.toList v)) []

reconstruct :: (Ord a, Show a) => G.SCC (a, S.Set a) -> M.Map a (S.Set a) -> M.Map a (S.Set a)
reconstruct (G.AcyclicSCC (k, v)) r
    = let v' = S.foldr (\k r' -> fromMaybe (error "reconstruct (AcyclicSCC)") (M.lookup k r) `S.union` r') v v
       in M.insert k v' r
reconstruct (G.CyclicSCC  kvs   ) r
    = let v  = S.unions (map snd kvs)
          v' = S.foldr (\k r' -> fromMaybe S.empty{-(error "reconstruct (CyclicSCC)")-} (M.lookup k r) `S.union` r') v v
       in foldr (\(k, _) -> M.insert k v') r kvs

-- | Logging

message :: String -> MyMonad ()
message m
    = do (s, s', ms) <- get
         put (s, s', ms ++ [m])
         return ()
               
-- | Inference tree (typing derivation)

type InferenceTree r = Z.TreePos Z.Full r

data Rule = W Constr Constr Subst
          | W' TyEnv Expr Ty Be Constr Subst
          deriving Show
             
down, up :: MyMonad ()
down = modifySnd (Z.insert emptyInferenceTree . Z.children)
up   = modifySnd (fromJust . Z.parent)

putRule :: Rule -> MyMonad ()
putRule = modifySnd . Z.setLabel

modifySnd :: (InferenceTree Rule -> InferenceTree Rule) -> MyMonad ()
modifySnd f = modify (\(a, b, c) -> (a, f b, c))

emptyInferenceTree = T.Node (error "derivation not specified") []

-- | Fresh identifiers

class Fresh a where 
    fresh :: MyMonad a
    
instance Fresh Name where
    fresh = do (x:xs, s', s'') <- get
               put (xs, s', s'')
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
    
instance (FV a, FV b) => FV (a, b) where
    ftv (x, y) = ftv x `S.union` ftv y
    fbv (x, y) = fbv x `S.union` fbv y
    
instance (FV a, Ord a) => FV (S.Set a) where
    ftv = unionMap ftv
    fbv = unionMap fbv

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

instance Substitute Subst where -- FIXME: dangerous to expose to the outside world...
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
