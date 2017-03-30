import Prelude hiding (map)

-- map can be implemented as a fold:
map :: (a -> b) -> [a] -> [b]
map f = foldr (\x xs -> (f x) : xs) [] 

-- map can be implemented from list comprehension
map' :: (a -> b) -> [a] -> [b]
map' f xs = [ f x | x <- xs ] 


main :: IO ()
main = do
  putStrLn $ show $ take 30 (map   (*3) [1..])
  putStrLn $ show $ take 30 (map'  (*3) [1..])

