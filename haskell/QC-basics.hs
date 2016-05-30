import Test.QuickCheck
import Data.List

qsort :: Ord a => [a] -> [a]
qsort [] = []
qsort (x:xs) = qsort lhs ++ [x] ++ qsort rhs
  where lhs = filter (< x) xs
        rhs = filter (>= x) xs


-- the qsort operation should be idempotent
prop_idempotent xs = qsort( qsort xs) == qsort xs

-- the head of sorted list should be the minimum
prop_minimum xs = (xs == []) || head (qsort xs) == minimum xs

-- alternatively
prop_minimum' xs = not (null xs) ==> head (qsort xs) == minimum xs

-- the output of qsort should be ordered
prop_ordered xs = ordered (qsort xs)
  where ordered []  = True
        ordered [x] = True
        ordered (x:y:xs) = (x <= y) && ordered (y:xs)

-- the output of qsort should be a permutation of the input
prop_permutation xs = permutation xs (qsort xs)
  where permutation xs ys = null (xs \\ys) && null (ys \\ xs)

-- the last element of sorted list should be the maximum
prop_maximum xs = not (null xs) ==> 
  last (qsort xs) == maximum xs


-- the output of sort should match some other reference 
-- (library in this case) This is a good reason to have 
-- prototype which, while inefficient is deemed correct.
prop_sort_model xs = sort xs == qsort xs


-- and despite all this, correctness is still uncertain
main = do
  quickCheck (prop_idempotent :: [Integer] -> Bool)
  quickCheck (prop_minimum :: [Integer] -> Bool)
  quickCheck (prop_minimum' :: [Integer] -> Property)
  quickCheck (prop_idempotent :: [Integer] -> Bool)
  quickCheck (prop_ordered :: [Integer] -> Bool)
  quickCheck (prop_permutation :: [Integer] -> Bool)
  quickCheck (prop_maximum :: [Integer] -> Property)
  quickCheck (prop_sort_model :: [Integer] -> Bool)



