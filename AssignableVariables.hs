module Main where

import Data.IORef

newVar = newIORef
(.=)   = writeIORef
deref  = readIORef

main = do x <- newVar 10
          y <- deref x
          x .= y + 10
          return x
          
main' = newIORef 10 >>= \x -> readIORef x >>= \y -> writeIORef x (y + 10) >> return x
