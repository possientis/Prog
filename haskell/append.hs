import Prelude hiding ((++))

-- not tail recursive
(<+>) :: [a] -> [a] -> [a]
[] <+> ys      = ys
(x:xs) <+> ys  = x : (xs <+> ys)  -- '<+>' binding more strongly than ':'

-- tail recursive but lazy, slower than <+>
(++) :: [a] -> [a] -> [a]
xs ++ ys = go (reverse xs) ys
  where
  go [] ys      = ys
  go (x:xs) ys  = go xs (x:ys)


-- tail recursive with some strict evaluation (doesnt help)
(<++>) :: [a] -> [a] -> [a]
xs <++> ys = let rev = (reverse xs) in seq rev (go rev ys)
  where
  go [] ys      = ys
  go (x:xs) ys  = go xs (x:ys)




main :: IO ()
main = do
  putStrLn $ show $ length ([1..5000000] <++> [1..5000000])
