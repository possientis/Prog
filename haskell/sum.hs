-- sum is a fold

import Prelude hiding (sum)

sum :: (Num a, Foldable t) => t a -> a
sum = foldr (+) 0 

main :: IO ()
main = do 
  putStrLn $ show $ sum [1..1000]

