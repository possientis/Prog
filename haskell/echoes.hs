echoes :: [Int] -> [Int]
echoes  = foldr (\x xs -> (replicate x x) ++ xs) []



main :: IO ()
main = do
  putStrLn $ show $ take 130 (echoes [1..])

