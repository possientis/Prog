-- does not compile
module Sorting where

import Control.Parallel (par, pseq)

-- quick sort algorithm
-- x is called the 'pivot'
-- need not be the first element, but this makes it
-- easier to pattern match on

sort :: (Ord a) => [a] -> [a]
sort (x:xs) = lesser ++ x:greater
  where lesser  = sort [y | y <- xs, y < x]
        greater = sort [y | y <- xs, x <= y]
sort _ = [] 


-- pseq guarantees that left argument evaluated before right
parSort :: (Ord a) => [a] -> [a]
parSort (x:xs) = force greater `par` (force lesser `pseq` (lesser ++ x:greater))
  where lesser  = parSort [y | y <- xs, y < x]
        greater = parSort [y | y <- xs, x <= y]
parSort _ = []


