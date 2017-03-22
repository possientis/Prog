-- product is a fold

import Prelude hiding (product)

product :: (Num a, Foldable t) => t a -> a
product = foldr (*) 1 

main :: IO ()
main = do 
  putStrLn $ show $ product [1..1000]

