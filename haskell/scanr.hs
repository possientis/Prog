--import Prelude hiding (scanr)

-- definition using recursion
scanr' :: (a -> b -> b) -> b -> [a] -> [b]
scanr' op acc []      = [acc]
scanr' op acc (x:xs)  = let ys = scanr' op acc xs 
                        in op x (head ys) : ys

-- definition using foldr
scanr'' :: (a -> b -> b) -> b -> [a] -> [b]
scanr'' op acc = foldr (\x ys -> op x (head ys) : ys) [acc]  

main :: IO()
main = do
  putStrLn $ show $ scanr   (+) 0 [1..30]
  putStrLn $ show $ scanr'  (+) 0 [1..30]
  putStrLn $ show $ scanr'' (+) 0 [1..30]
  putStrLn $ show $ scanr   (*) 1 [1..15]
  putStrLn $ show $ scanr'  (*) 1 [1..15]
  putStrLn $ show $ scanr'' (*) 1 [1..15]
 
