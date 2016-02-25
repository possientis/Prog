import Data.List  -- foldl' efficient foldl 

main = do
--  this will even crash linux
--  putStrLn (show (foldl  (+) 0 [1..100000000]))

-- this will not crash linux
    putStrLn (show (foldl' (+) 0 [1..100000000]))
