-- or is a fold

import Prelude hiding (or)

or :: Foldable t => t Bool -> Bool
or = foldr (||) False

main :: IO ()
main = do 
  putStrLn $ show $ or []
  putStrLn $ show $ or [False, False, True, (error "don't worry") , False]
  putStrLn $ show $ or [False, False, False, False, False]



