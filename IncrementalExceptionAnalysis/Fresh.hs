{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Fresh where -- FIXME: Does substantially more than generating fresh variables

import Control.Monad
import Control.Monad.State

import           Data.Maybe
import qualified Data.Tree        as T
import qualified Data.Tree.Zipper as Z      -- rosezipper-0.2

-- | Fresh identifiers

type Ident = String

class Fresh a where 
    fresh :: State ([Ident], s') a
    
instance Fresh Ident where
    fresh = do ((x:xs), s') <- get
               put (xs, s')
               return x
               
freshIdents = map (\n -> "_{" ++ show n ++ "}") [1..]

-- | Inference tree (typing derivation)

type InferenceTree r = Z.TreePos Z.Full r
             
down, up :: State (s', InferenceTree r) ()
down = modifySnd (Z.insert emptyInferenceTree . Z.children)
up   = modifySnd (fromJust . Z.parent)

putRule :: r -> State (s', InferenceTree r) ()
putRule = modifySnd . Z.setLabel

modifySnd :: (s -> s) -> State (s', s) ()
modifySnd f = modify (\(a,b) -> (a, f b))

emptyInferenceTree = T.Node (error "derivation not specified") []

-- | Initial state

initialState = (freshIdents, Z.fromTree emptyInferenceTree)
