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

-- not clear why this works
force :: [a] -> ()
force xs = go xs `pseq` ()  -- pseq :: a -> b -> b
  where go (_:xs) = go xs
        go [] = 1

-- same code as parSort (below) but without forcing. 
-- because of lazy evaluation, almost no valuable work is done
-- by alternative threads, hence evaluation is almost sequential.
sillySort :: (Ord a) => [a] -> [a]
-- par :: a -> b -> b
-- pseq :: a -> b -> b
sillySort (x:xs) = greater `par` (lesser `pseq` (lesser ++ x:greater))
  where lesser  = sillySort [y | y <- xs, y < x]
        greater = sillySort [y | y <- xs, x <= y]
sillySort _ = []

-- pseq guarantees that left argument evaluated before right
-- pseq :: a -> b -> b
{-
 - The par function does not actually promise to evaluate an expression in parallel with
 - another. Instead, it undertakes to do so if it “makes sense.” This wishy-washy non-
 - promise is actually more useful than a guarantee to always evaluate an expression in
 - parallel. It gives the runtime system the freedom to act intelligently when it encounters
 - par . 
-}

parSort :: (Ord a) => [a] -> [a]
parSort (x:xs) = force greater `par` (force lesser `pseq` (lesser ++ x:greater))
  where lesser  = parSort [y | y <- xs, y < x]
        greater = parSort [y | y <- xs, x <= y]
parSort _ = []


