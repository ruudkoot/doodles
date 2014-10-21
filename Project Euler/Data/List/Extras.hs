module Data.List.Extras (
    takeLast
) where

takeLast n xs = drop (length xs - n) xs
