module Algorithms where

import qualified Prelude
import Prelude(Int,($),return)
import Imperative

insertionSort :: MonadImperative m => Arr m Int -> m (Arr m Int)
insertionSort a = do
    i <- new int
    j <- new int
    for j from 2 to (length a) $ do
        key <- a(j)
        i <<- j-1
        while (i > 0 && a(i) > key) $ do
            () <- set a(i+1) a(i)
            i <<- i-1
        set' a(i+1) key
    return a
