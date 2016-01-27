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



