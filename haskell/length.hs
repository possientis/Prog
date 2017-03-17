import Prelude hiding (length)

-- not tail recursive implementation
-- stack overflow for  [1..50000000] on ghci
-- fine on ghc -O2 for [1..500000000]

length' :: [a] -> Int
length' [] = 0
length' (x:xs) = 1 + length' xs


-- this seems to be twice as fast on ghc -O2 for [1..500000000]
length :: [a] -> Int
length = go 0
  where
  go n [] = n
  go n (x:xs) = go (n+1) xs


main :: IO ()
main = do
  putStrLn $ show (length [1..500000000])
