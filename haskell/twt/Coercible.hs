{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE RoleAnnotations        #-}


import Data.Coerce

newtype Sum a = Sum 
    { getSum :: a 
    }

newtype ZipList a = ZipList 
    { getZipList :: [a] 
    }

instance Semigroup (Sum Int) where
    (<>) (Sum x) (Sum y) = Sum (x + y)

instance Monoid (Sum Int) where
    mempty = Sum 0


slowSum :: [Int] -> Int
slowSum = getSum . mconcat . fmap Sum

fastSum :: [Int] -> Int
fastSum = getSum . mconcat . coerce


newtype Reverse a = Reverse
    { getReverse :: a 
    } deriving (Eq, Show)

instance (Ord a) => (Ord (Reverse a)) where
    compare (Reverse x) (Reverse y) = compare y x


data BST v
    = Empty
    | Branch (BST v) v (BST v)

-- Memory layout of values of type BST v will depend on instance Ord v
-- so it should not be the case that Coercible v v' => Coercible (BST v) (BST v')
-- Strengthening role from representational to nominal
type role BST nominal
-- type role BST representational  -- works but does nothing, representational by default


