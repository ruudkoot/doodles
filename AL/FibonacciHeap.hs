{-# LANGUAGE StandaloneDeriving #-}

module Main where

import Prelude hiding (min)

import Data.IORef

instance Show (IORef a) where
    show _ = "<IORef>"
    
instance Show (IO a) where
    show _ = "<IO>"

data Heap a = Heap { min :: Maybe (IO (IORef (Node a)))
                   , n   :: Int                         }
            deriving Show

data Node a = Node { left, right ::        IO (IORef (Node a))
                                 -- can we get rid of the IO by using a fixpoint somewhere?
                   , p, child    :: Maybe (IO (IORef (Node a)))
                                 -- maybe we should move maybe inside IO or even IORef
                   , mark        :: Bool
                   , degree      :: Int                     
                   , x           :: a                           }
            deriving Show
          
empty :: IO (Heap a)
empty = return $ Heap {min = Nothing, n = 0}

node :: a -> IO (Node a)
node x = do let n = Node { degree = 0
                         , p      = Nothing
                         , child  = Nothing
                         , left   = newIORef n
                         , right  = newIORef n
                         , mark   = False      
                         , x      = x          } -- note the recursion here
            return n
                 
insert :: Heap a -> Node a -> IO (Heap a)
insert h x = 
                case min h of
                  Nothing -> return $ Heap {min = Just (newIORef x), n = 1}
                  Just r  -> undefined


