-- recursive foldr, not iterative, not stack friendly
myFoldr :: (a -> b -> b) -> b -> [a] -> b  
myFoldr op init [] = init
myFoldr op init (x:xs) = op x (myFoldr op init xs)

mySum :: (Num a) => [a] -> a
mySum = myFoldr (+) 0


iterFoldr :: (a -> b -> b) -> b -> [a] -> b
iterFoldr op init xs = loop op init (reverse xs)  where
  loop :: (a -> b -> b) -> b -> [a]-> b
  loop op acc []      = acc
  loop op acc (x:xs)  = loop op (op x acc) xs

iterSum :: (Num a) => [a] -> a
iterSum = iterFoldr (+) 0

iterCheck :: String -> String
iterCheck = iterFoldr (:) []

iterLeft :: String -> String
iterLeft = foldl (\x -> \y -> (y:x))  []


