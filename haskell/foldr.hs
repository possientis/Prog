import Prelude hiding (foldr)

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr op acc []     = acc
foldr op acc (x:xs) = op x (foldr op acc xs) 
