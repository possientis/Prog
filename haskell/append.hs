import Prelude hiding ((++))

-- not tail recursive
(<+>) :: [a] -> [a] -> [a]
[] <+> ys      = ys
(x:xs) <+> ys  = x : xs <+> ys  -- '<+>' binding more strongly than ':'


main :: IO ()
main = do
  putStrLn $ "Hello " <+> "World!"
