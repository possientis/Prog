-- maximum is a fold

import Prelude hiding (maximum)

maximum :: (Foldable t, Ord a) => t a -> a
maximum = foldr1 max 



main :: IO ()
main = do
  putStrLn $ show $ maximum [1..5000000]
