--import Prelude hiding (scanl)
--import Prelude hiding (scanl')

-- definition using recursion
scanl' :: (b -> a -> b) -> b -> [a] -> [b]
scanl' op acc []     = [acc]
scanl' op acc (x:xs) = acc : scanl' op (op acc x) xs 


--definition using foldl
scanl'' :: (b -> a -> b) -> b -> [a] -> [b]
scanl'' op acc = foldl (\ys x -> ys ++ [op (last ys) x]) [acc]



main :: IO()
main = do
  putStrLn $ show $ scanl   (+) 0 [1..30]
  putStrLn $ show $ scanl'  (+) 0 [1..30]
  putStrLn $ show $ scanl'' (+) 0 [1..30]
  putStrLn $ show $ scanl   (*) 1 [1..15]
  putStrLn $ show $ scanl'  (*) 1 [1..15]
  putStrLn $ show $ scanl'' (*) 1 [1..15]
