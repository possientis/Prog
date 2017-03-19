import Prelude hiding (take)


-- not tail recursive
take :: Int -> [a] -> [a]
take 0 xs     = []
take n []     = error "take: list does not have enough elements"
take n (x:xs) = x : take (n-1) xs 


main :: IO ()
main = do
  putStrLn $ show $ length $ take 2000000 [1..5000000]

