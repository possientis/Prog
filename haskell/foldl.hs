import Data.List  -- foldl' efficient foldl 

-- just to ensure successful compilation
someFunc x = x
anotherFunc x y = y

main = do
--  this will even crash linux
--  putStrLn (show (foldl  (+) 0 [1..100000000]))

-- this will not crash linux
-- this foldl uses strict evaluation
    putStrLn (show (foldl' (+) 0 [1..100000000]))

-- the implementation of foldl' goes as follows using 'seq'
foldl'' _    zero [] = zero
foldl'' step zero (x:xs) = 
  let new = step zero x
  -- the 'seq' function is akin to 'force' in scheme
  -- it forces the evaluation of the first argument and returns the second
  -- it does not actually do anything with the first argument except of
  -- course if it is used in the expression forming the second argument.
  in new `seq` foldl'' step new xs -- use of the 'seq' function 
-- the use of 'seq' forces evaluation and prevents space blow up


-- on the appropriate use of seq

-- incorrect: seq is hidden by the application of someFunc
-- since someFunc will be evaluated first, seq may occur too late
hiddenInside x y = someFunc (x `seq` y)

-- incorrect: a variation of the above
hiddenbyLet x y z = let a = x `seq` someFunc y
  in anotherFunc a z

-- correct: seq will be evaluated first, forcing evaluation of x
onTheOutside x y = x `seq` someFunc y

chained x y z = x `seq` y `seq` someFunc z -- seq x (seq y someFunc z) `seq` can only be right associative

-- common mistake: use seq with two unrelated expression
-- strictly evaluating the first occurrence of (step zero x)
-- has no effect on the second.
badExpression step zero (x:xs) =
  seq (step zero x) (badExpression step (step zero x) xs) 

goodExpression step zero (x:xs) =
  let new = step zero x
  in new `seq` goodExpression step new xs


------------------------------------------------------------------------------
-- when evaluating an expression, seq stops as soon as it reaches a constructor
-- ---------------------------------------------------------------------------

l = let  value = (1+2):(3+4):[]  in seq value value -- seq will stop when it reaches (:)
p = let value =((1+2),(3+4)) in seq value value     -- seq does nothing to thunks inside pair


strictPair (a,b) = a `seq` b `seq` (a,b)
strictList (x:xs) = x `seq` x:strictList xs
strictList [] = []

