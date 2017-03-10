import Prelude hiding (abs)

abs x 
  | x < 0 = 0 - x 
  | otherwise = x

abs' x = 
  if x < 0 then 0 - x else x

abs'' x = 
  case x < 0 of
    True  -> 0 - x
    False -> x
    

