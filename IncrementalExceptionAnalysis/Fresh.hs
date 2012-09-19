{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Fresh where

import Control.Monad.State

type Ident = String

class Fresh a where 
    fresh :: State [Ident] a
    
instance Fresh Ident where
    fresh = do (x:xs) <- get
               put xs
               return x
               
freshIdents = map (\n -> "_{" ++ show n ++ "}") [1..]
