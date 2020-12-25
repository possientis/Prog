module  RanAccess 
    (   RAList  (..)
    ,   Digit   (..)
    ,   fromRA
    ,   fetchRA
    ,   fetch
    )   where

import Tree

data Digit a = Zero | One (Tree a)

-- random access list
newtype RAList a = RAList { unRAList :: [Digit a] }

fromRA :: RAList a -> [a]
fromRA = concatMap from . unRAList
    where
        from :: Digit a -> [a]
        from Zero = []
        from (One t) = fromT t
        -- fromT can be made more efficient
        fromT :: Tree a -> [a]
        fromT (Leaf x) = [x]
        fromT (Node _ t1 t2) = fromT t1 ++ fromT t2

fetchRA :: Int -> RAList a -> Maybe a
fetchRA _ (RAList []) = Nothing
fetchRA k (RAList (Zero : xs)) = fetchRA k (RAList xs)
fetchRA k (RAList (One t : xs)) = if k < size t 
    then fetchT k t
    else fetchRA (k - size t) (RAList xs)
    where
        fetchT :: Int -> Tree a -> Maybe a
        fetchT k' _ | k' < 0     = Nothing
        fetchT 0 (Leaf x)        = Just x  
        fetchT _ (Leaf _)        = Nothing 
        fetchT k' (Node n t1 t2) = if k' < m
            then fetchT k' t1
            else fetchT (k' - m) t2
            where
                m = n `div` 2

fetch :: Int -> [a] -> Maybe a
fetch k xs = if 0 <= k && k < length xs then Just (xs !! k)  else Nothing
