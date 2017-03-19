import Prelude hiding ((++))

-- not tail recursive
(<+>) :: [a] -> [a] -> [a]
[] <+> ys      = ys
(x:xs) <+> ys  = x : xs <+> ys  -- '<+>' binding more strongly than ':'


(++) :: [a] -> [a] -> [a]
xs ++ ys = go (reverse xs) ys
  where
  go [] ys      = ys
  go (x:xs) ys  = go xs (x:ys)


main :: IO ()
main = do
  putStrLn $ "Hello " ++ "World!"
