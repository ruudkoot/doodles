add :: Maybe Int -> Maybe Int -> Maybe Int
add mx my = case mx of
              Nothing -> Nothing
              Just x  -> case my of
                           Nothing -> Nothing
                           Just y  -> Just (x + y)
                           
add2 :: Monad m => m Int -> m Int -> m Int
add2 mx my = do
    x <- mx
    y <- my
    return (x + y)
