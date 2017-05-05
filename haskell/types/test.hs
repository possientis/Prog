f :: Bool -> Maybe Int
f x | False = Just 1
f x | True  = Just 2


main = do
  print $ f True
  print $ f False
