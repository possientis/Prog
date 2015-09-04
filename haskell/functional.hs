twice :: (a -> a) -> (a-> a)
twice f x = f (f x)

myTwice :: (a -> a) -> (a -> a)
myTwice f = f.f

myMap :: (a -> b) -> ([a] -> [b])
myMap f [] = []
myMap f (x:xs) = f x : myMap f xs

yourMap f xs = [f x | x <- xs]

myFilter :: (a -> Bool) -> ([a] -> [a])
myFilter p xs = [x | x <- xs, p x]

yourFilter :: (a -> Bool) -> ([a] -> [a])
yourFilter p [] = []
yourFilter p (x:xs)
  | p x       = x : yourFilter p xs
  | otherwise =     yourFilter p xs

myFoldr :: (a -> b -> b) -> b -> ([a] -> b)
myFoldr op v [] = v
myFoldr op v (x:xs) = x `op` myFoldr op v xs

mySum = myFoldr (+) 0
myProduct = myFoldr (*) 1
myOr = myFoldr (||) False
myAnd = myFoldr (&&) True
myLength = myFoldr (\_ -> \y -> (1 + y)) 0
yourLength = sum . map (\_ -> 1)
myReverse = myFoldr (\x -> \y -> y ++ [x]) []
myAppend xs ys = myFoldr (:) ys xs

(£) :: (b -> c) -> (a -> b) -> (a -> c)
g £ f = \x -> g (f x)



