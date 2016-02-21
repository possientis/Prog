import Data.Char (digitToInt)

asInt :: String -> Int
asInt xs = loop xs 0 where
  loop [] acc = acc
  loop (x:xs) acc = loop xs (10 * acc + digitToInt x)

asInt' :: String -> Int
asInt' = foldl  (\x -> \c -> x *10 + digitToInt c) 0
