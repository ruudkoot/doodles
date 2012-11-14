{-# LANGUAGE GADTs, DataKinds, KindSignatures, Rank2Types, StandaloneDeriving #-}

-- | Sized lists

-- * Lists can be non-empty or possible empty

data Size
    =  E -- possibly empty
    | NE -- definitely not empty

data List a (size :: Size) where
    Nil  ::                  List a E
    Cons :: a -> List a s -> List a t
    
deriving instance Show a => Show (List a s)

-- instance Functor (List s) -- FIXME: swap arguments...

-- * Forget the size of non-empty list
    
forget :: List a s -> List a E
forget Nil         = Nil
forget (Cons a as) = Cons a (forget as)

-- * Total pattern-matching on sized lists

match :: List a s -> (r, (a, List a E) -> r) -> r
match Nil         (r, _) = r
match (Cons a as) (_, e) = e (a, forget as)

matchNE :: List a NE -> ((a, List a E) -> r) -> r
matchNE (Cons a as) e = e (a, forget as)

-- * Total (depenent?) pattern-matching on sized lists

depMatch :: List a s -> (r s, (a, List a E) -> r s) -> r s
depMatch Nil         (r, _) = r
depMatch (Cons a as) (_, e) = e (a, forget as)

-- * Conversion from regular lists

toList :: [a] -> List a E
toList [    ] = Nil
toList (x:xs) = Cons x (toList xs)

fromList :: List a s -> [a]
fromList Nil         = []
fromList (Cons x xs) = x : fromList xs

-- | Type-safe "risers" (using only total pattern-matching)

-- * Attempt 1 (Fails because the target type is not polymorphic enough)

risers1 :: List Int E -> List (List Int E) E
risers1 as =
    match as
        (               Nil
        , \(x1, xxs) -> match xxs
                            (              Cons (Cons x1 Nil) Nil
                            , \(x2, xs) -> matchNE (undefined (Cons x2 xs)) -- !!
                                                (\(s,ss) ->
                                                    if x1 < x2
                                                    then Cons (Cons x1   s)         ss
                                                    else Cons (Cons x1 Nil) (Cons s ss)
                                                ) 
                                                        
                            )
        )

-- * Attempt 2
risers2 :: forall (s :: Size). List Int s -> List (List Int E) s
risers2 as =
    match as
        (               undefined -- !!
        , \(x1, xxs) -> match xxs
                            (              Cons (Cons x1 Nil) Nil
                            , \(x2, xs) -> matchNE (risers2 (Cons x2 xs))
                                                (\(s,ss) ->
                                                    if x1 < x2
                                                    then Cons (Cons x1   s)         ss
                                                    else Cons (Cons x1 Nil) (Cons s ss)
                                                ) 
                                                        
                            )
        )
-- * Attempt 3 (Dependent pattern-matching?)
risers3 :: forall (s :: Size). List Int s -> List (List Int E) s
risers3 as =
    depMatch as
        (               undefined -- !!
        , \(x1, xxs) -> match xxs
                            (              Cons (Cons x1 Nil) Nil
                            , \(x2, xs) -> matchNE (risers3 (Cons x2 xs))
                                                (\(s,ss) ->
                                                    if x1 < x2
                                                    then Cons (Cons x1   s)         ss
                                                    else Cons (Cons x1 Nil) (Cons s ss)
                                                ) 
                                                        
                            )
        )

