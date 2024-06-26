{-# OPTIONS_GHC -fno-full-laziness    #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Stitch.Data.IHashMap.List
  ( deleteBy
  , isPermutationBy
  , unorderedCompare
  ) where

import Data.Maybe
import Data.List (sortBy)

-- Note: previous implemenation isPermutation = null (as // bs)
-- was O(n^2) too.
--
-- This assumes lists are of equal length
isPermutationBy :: (a -> b -> Bool) -> [a] -> [b] -> Bool
isPermutationBy f = go
  where
    f' = flip f

    go [] [] = True
    go (x : xs) (y : ys)
        | f x y         = go xs ys
        | otherwise     = fromMaybe False $ do
            xs' <- deleteBy f' y xs
            ys' <- deleteBy f x ys
            return (go xs' ys')
    go [] (_ : _) = False
    go (_ : _) [] = False

-- The idea:
--
-- Homogeonous version
--
-- uc :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
-- uc c as bs = compare (sortBy c as) (sortBy c bs)
--
-- But as we have only (a -> b -> Ordering), we cannot directly compare
-- elements from the same list.
--
-- So when comparing elements from the list, we count how many elements are
-- "less and greater" in the other list, and use the count as a metric.
--
unorderedCompare :: (a -> b -> Ordering) -> [a] -> [b] -> Ordering
unorderedCompare c as bs = go (sortBy cmpA as) (sortBy cmpB bs)
  where
    go [] []      = EQ
    go [] (_ : _) = LT
    go (_ : _) [] = GT
    go (x : xs) (y : ys) = c x y `mappend` go xs ys

    cmpA a a' = compare (inB a) (inB a')
    cmpB b b' = compare (inA b) (inA b')

    inB a = ( length $ filter (\b -> c a b == GT) bs
            , negate $ length $ filter (\b -> c a b == LT) bs
            )
    inA b = ( length $ filter (\a -> c a b == LT) as
            , negate $ length $ filter (\a -> c a b == GT) as
            )

-- Returns Nothing is nothing deleted
deleteBy              :: (a -> b -> Bool) -> a -> [b] -> Maybe [b]
deleteBy _  _ []      = Nothing
deleteBy eq x (y:ys)  = if x `eq` y then Just ys else fmap (y :) (deleteBy eq x ys)
