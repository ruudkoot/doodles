module Main where

import Data.IORef

data List = Nil | Cons Int (IORef List)

instance Show List where
    show Nil        = "Nil"
    show (Cons n _) = "(Cons " ++ show n ++ ")"

cons :: Int -> List -> IO List
cons n l = do l' <- newIORef l
              return (Cons n l')


              
conv :: List -> IO [Int]
conv Nil        = return []
conv (Cons n t) = do t' <- readIORef t
                     t'' <- conv t'
                     return (n : t'')
              
main = do xs <- cons 5 Nil
          return xs
