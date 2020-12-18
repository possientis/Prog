module  RanAccess 
    (   RAList  (..)
    ,   Digit   (..)
    ,   fromRA
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


