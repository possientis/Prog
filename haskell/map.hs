-- map can be implemented as a fold:
import Prelude hiding (map)

map :: (a -> b) -> [a] -> [b]
map f = foldr (\x xs -> (f x) : xs) [] 


main :: IO ()
main = do
  putStrLn $ show $ take 100 (map (*3) [1..])

