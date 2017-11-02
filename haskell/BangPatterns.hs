{-# LANGUAGE BangPatterns #-}

import Prelude hiding (sum)


sum :: Num a => [a] -> a
sum xs = go 0 xs where
    -- building a long chain of thunks due to non-strict evaluation
    -- -O2 compiler option actually removes the performance penalty here 
    go n (x:xs) = go (n + x) xs 
    go n []     = n


sum' :: Num a => [a] -> a
sum' xs = go 0 xs where
    -- bang pattern forcing WHNF evaluation of argument
    -- providing a significant performance improvement
    go !n (x:xs) = go (n + x) xs 
    go n []     = n

-- bang pattern is syntactic sugar for the following 
sum'' :: Num a => [a] -> a
sum'' xs = go 0 xs where
    go n _ | n `seq` False  = undefined
    go n (x:xs)             = go (n + x) xs
    go n []                 = n 


-- bang pattern only works in pattern
-- cannot define f $! x as 'f !x'
($!) :: (a -> b) -> a -> b
f $! x = let !y = x in f y

main :: IO ()
main = do
    putStrLn $ show $ sum'' [1..5000000]


