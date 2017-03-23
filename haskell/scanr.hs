--import Prelude hiding (scanr)

-- returns initial segments of a list
initials :: [a] -> [[a]]
initials []      = [[]]
initials (x:xs)  = []:map (x:) (initials xs)

scanr' :: (a -> b -> b) -> b -> [a] -> [b]
scanr' op acc = map (foldr op acc) . initials


main :: IO()
main = do
  putStrLn $ show $ scanr  (+) 0 [1..30]
  putStrLn $ show $ scanr' (+) 0 [1..30]
  putStrLn $ show $ scanr' (*) 1 [1..15]
  putStrLn $ show $ scanr  (*) 1 [1..15]
 
