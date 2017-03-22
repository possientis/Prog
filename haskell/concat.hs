-- concat is a fold

import Prelude hiding (concat)

concat :: Foldable t => t [a] -> [a]
concat = foldr (++) [] 

main :: IO ()
main = do 
  putStrLn $ show $ concat ["hello", " how", " are", " you?"]

