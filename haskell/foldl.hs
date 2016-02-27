import Data.List  -- foldl' efficient foldl 

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

