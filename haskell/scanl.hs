import Prelude hiding (scanl)

scanl :: (b -> a -> b) -> b -> [a] -> [b]
scanl op acc []     = [acc]
scanl op acc (x:xs) = acc : scanl op (op acc x) xs 


scanl' :: (b -> a -> b) -> b -> [a] -> [b]
scanl' op acc = foldl (\xs x -> xs ++ [op (last xs) x]) [acc]

-- returns initial segments of a list
initials :: [a] -> [[a]]
initials []      = [[]]
initials (x:xs)  = []:map (x:) (initials xs)

scanl'' :: (b -> a -> b) -> b -> [a] -> [b]
scanl'' op acc = map (foldl op acc) . initials



main :: IO()
main = do
  putStrLn $ show $ scanl   (+) 0 [1..30]
  putStrLn $ show $ scanl'  (+) 0 [1..30]
  putStrLn $ show $ scanl'' (+) 0 [1..30]
  putStrLn $ show $ scanl   (*) 1 [1..15]
  putStrLn $ show $ scanl'  (*) 1 [1..15]
  putStrLn $ show $ scanl'' (*) 1 [1..15]
