module Danvy where

import Control.Applicative
import Control.Monad
import Data.Maybe

data Mobile
    = OBJ Int
    | BAR Int Mobile Mobile
    deriving (Eq, Ord, Show)
    
m1 = BAR 1 (BAR 1 (OBJ 2) (OBJ 2)) (OBJ 5)
m2 = BAR 1 (OBJ 6) (BAR 1 (OBJ 2) (OBJ 9))

weight m
    = let visit (OBJ n)       = n
          visit (BAR n m1 m2) = n + visit m1 + visit m2
       in visit m
       
equil0 m
    = let visit (OBJ n)       = True
          visit (BAR n m1 m2) = weight m1 == weight m2 && visit m1 && visit m2
       in visit m

lift1 :: (a -> Maybe b) -> Maybe a -> Maybe b
lift1 f (Just v) = f v
lift1 f _        = Nothing

lift2 :: ((a, b) -> Maybe c) -> (Maybe a, Maybe b) -> Maybe c
lift2 f (Just v1, Just v2) = f (v1, v2)
lift2 f _                  = Nothing

equil1 m
    = let visit (OBJ n)       = Just n
          visit (BAR n m1 m2) = lift2 (\(n1, n2) -> if n1 == n2
                                                    then Just (n + n1 + n2)
                                                    else Nothing)
                                      (visit m1, visit m2)
       in isJust (visit m)

equil2 m
    = let visit (OBJ n)       = Just n
          visit (BAR n m1 m2) = lift1 (\n1 ->
                                        lift1 (\n2 ->
                                                if n1 == n2
                                                then Just (n + n1 + n2)
                                                else Nothing)
                                              (visit m2))
                                      (visit m1)
       in isJust (visit m)
       
equil2M m
    = let visit (OBJ n)       = return n
          visit (BAR n m1 m2) = do n1 <- visit m1
                                   n2 <- visit m2
                                   if n1 == n2
                                   then return (n + n1 + n2)
                                   else fail "unbalanced"
       in isJust (visit m)

-- equil3

equil4 m
    = let visit :: Mobile -> (Maybe Int -> Bool) -> Bool
          visit (OBJ n)       k
            = k (Just n)
          visit (BAR n m1 m2) k
            = visit m1 (\v1 ->
                         case v1 of
                             (Just n1) -> visit m2 (\v2 ->
                                                     case v2 of
                                                       (Just n2) ->
                                                            if n1 == n2
                                                            then k (Just (n + n1 + n2))
                                                            else k Nothing
                                                       Nothing   -> k Nothing
                                                   )
                             Nothing   -> k Nothing
                       )
       in visit m isJust

equil5 m
    = let visit :: Mobile -> (Int -> Bool) -> (() -> Bool) -> Bool
          visit (OBJ n)       ki ku
            = ki n
          visit (BAR n m1 m2) ki ku
            = visit m1 (\n1 -> visit m2
                                     (\n2 -> if n1 == n2
                                             then ki (n + n1 + n2)
                                             else ku ())
                                     ku)
                       ku
       in visit m (const True) (const False)

equil5' m
    = let visit :: Mobile -> (Int -> Bool) -> Bool -> Bool
          visit (OBJ n)       ki ku
            = ki n
          visit (BAR n m1 m2) ki ku
            = visit m1 (\n1 -> visit m2
                                     (\n2 -> if n1 == n2
                                             then ki (n + n1 + n2)
                                             else ku)
                                     ku)
                       ku
       in visit m (const True) False

equil6 m
    = let visit :: Mobile -> (Int -> Bool) -> Bool
          visit (OBJ n)       k
            = k n
          visit (BAR n m1 m2) k
            = visit m1 (\n1 -> visit m2
                                     (\n2 -> if n1 == n2
                                             then k (n + n1 + n2)
                                             else False))
       in visit m (const True)

-- equil7

data Cont = C0
          | C1 Int Mobile Cont
          | C2 Int Int Cont
          deriving (Eq, Ord, Show)

equil8 m
    = let
        apply_cont :: Cont -> Int -> Bool
        apply_cont C0 _
            = True
        apply_cont (C1 n m2 c) n1
            = visit m2 (C2 n n1 c)
        apply_cont (C2 n n1 c) n2
            = if n1 == n2 then apply_cont c (n + n1 + n2) else False

        visit :: Mobile -> Cont -> Bool
        visit (OBJ n) c
            = apply_cont c n
        visit (BAR n m1 m2) c
            = visit m1 (C1 n m2 c)
      in visit m C0

data Frame = F1 Int Mobile
           | F2 Int Int
           deriving (Eq, Ord, Show)
           
type Cont' = [Frame]

equil9 m
    = let
        pop_frame :: Cont' -> Int -> Bool
        pop_frame [] _
            = True
        pop_frame (F1 n m2 : c) n1
            = visit m2 (F2 n n1 : c)
        pop_frame (F2 n n1 : c) n2
            = if n1 == n2 then pop_frame c (n + n1 + n2) else False
        
        visit :: Mobile -> Cont' -> Bool
        visit (OBJ n) c
            = pop_frame c n
        visit (BAR n m1 m2) c
            = visit m1 (F1 n m2 : c)
      in visit m []
