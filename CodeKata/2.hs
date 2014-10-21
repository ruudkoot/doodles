module Main where

import Data.Array

-- | Kata

-- * 1

chop :: (Enum i, Ix i, Ord a) => a -> Array i a -> Maybe i
chop x a =
    let
        chop' i j
            | j < i     = Nothing
            | otherwise = let k = (i + j) `div` 2
                           in case compare (a ! toEnum k) x of
                                EQ -> Just (toEnum k)
                                LT -> chop' (k + 1) j
                                GT -> chop' i (k - 1)

        (i, j) = bounds a
    in 
        chop' (fromEnum i') (fromEnum j')

-- | Tests

fromList :: [a] -> Array Int a
fromList xs = listArray (0, length xs - 1) xs

assert_equal :: (Eq a, Monad m) => a -> a -> m ()
assert_equal x y
    | x == y    = return ()
    | otherwise = fail "assertion failed"

test_chop :: IO ()
test_chop = do
    assert_equal Nothing  (chop 3 (fromList []))
    assert_equal Nothing  (chop 3 (fromList [1]))
    assert_equal (Just 0) (chop 1 (fromList [1]))

    assert_equal (Just 0) (chop 1 (fromList [1, 3, 5]))
    assert_equal (Just 1) (chop 3 (fromList [1, 3, 5]))
    assert_equal (Just 2) (chop 5 (fromList [1, 3, 5]))
    assert_equal Nothing  (chop 0 (fromList [1, 3, 5]))
    assert_equal Nothing  (chop 2 (fromList [1, 3, 5]))
    assert_equal Nothing  (chop 4 (fromList [1, 3, 5]))
    assert_equal Nothing  (chop 6 (fromList [1, 3, 5]))

    assert_equal (Just 0) (chop 1 (fromList [1, 3, 5, 7]))
    assert_equal (Just 1) (chop 3 (fromList [1, 3, 5, 7]))
    assert_equal (Just 2) (chop 5 (fromList [1, 3, 5, 7]))
    assert_equal (Just 3) (chop 7 (fromList [1, 3, 5, 7]))
    assert_equal Nothing  (chop 0 (fromList [1, 3, 5, 7]))
    assert_equal Nothing  (chop 2 (fromList [1, 3, 5, 7]))
    assert_equal Nothing  (chop 4 (fromList [1, 3, 5, 7]))
    assert_equal Nothing  (chop 6 (fromList [1, 3, 5, 7]))
    assert_equal Nothing  (chop 8 (fromList [1, 3, 5, 7]))
