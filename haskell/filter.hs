import Prelude hiding (filter)


filter :: (a -> Bool) -> [a] -> [a]
filter p xs = [ x | x <- xs, p x]

filter' :: (a -> Bool) -> [a] -> [a]
filter' p []      = []
filter' p (x:xs)  = if p x then x:ys else ys 
  where ys = filter p xs

main :: IO ()
main = do 
  putStrLn $ show $ filter  even [1..20]
  putStrLn $ show $ filter' even [1..20]
