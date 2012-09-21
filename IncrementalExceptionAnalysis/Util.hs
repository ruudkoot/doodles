module Util where

import qualified Data.Set as S

flattenSetOfSets :: Ord a => S.Set (S.Set a) -> S.Set a
flattenSetOfSets = S.unions . S.toList
