module  SumUpTo
    (   main
    )   where

import Prelude  hiding (sum)

main :: IO ()
main = do
    print $ sum 0 (upto 1 1000000)

upto :: Integer -> Integer -> [Integer]
upto m n = if m > n 
    then []
    else m : upto (m + 1) n

sum :: Integer -> [Integer] -> Integer
sum n l = case l of
    []      -> n
    (x:xs)  -> sum (n + x) xs
