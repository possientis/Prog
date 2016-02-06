-- You have a building in 100 floors and many identical eggs.
-- Find out the highest floor from which an egg can be thrown
-- without breaking. You are only allowed to break two eggs.
-- Obviously you can start dropping an egg from floor one,
-- then from floor 2, then from floor 3 ... and stop when
-- an egg gets broken. This will give you the answer while
-- only breaking one egg and not two. However, what you want 
-- to know the minimal number of drops required to obtain 
-- the answer, while breaking no more than 2 eggs. Hence:
--
-- Question: what is the minimal number of drops required
-- in order to determine the highest floor from which an
-- egg can be dropped without breaking (ground floor or 100)
-- while breaking no more than two eggs in the process


-- Remark:
-- lazy evaluation still requires memoization
fib n
  | n < 0   = 1
  | n == 0  = 1
  | n == 1  = 1
  | n > 1   = fib (n - 1) + fib (n - 2)
-- the same issue will arise when implementing
-- dynamic programming with a recursive algorithm

-- complexity of this too high
g 0 = 0
g n = minimum [max x (1 + g (n - x)) | x <- [1..n]]

-- complexity fine here
h 0 = [0]
h n  = xs ++ [minimum (zipWith max (map (+1) xs) [n,(n-1)..1])] where
  xs = h (n - 1)

-- even simpler
-- if you are allowed to play say 10 moves, then you cannot afford to test 
-- a floor higher than 10 on the first drop (if the egg breaks you are
-- screwed). On the second drop, you cannot afford to test higher than 19.
-- Then 27 etc. 10 + .. + 1 = 55 so you can only cover 55 floors with 10
-- drops. you are looking for the smallest N such that 100 <= N(N+1)/2
-- which is 14. This works because you test 14. if it breaks you are 
-- good, if it doesnt you test 27. If it breaks you are goo otherwise 
-- you test 39 etc. 

