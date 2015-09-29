doubleUs x y = doubleMe x + doubleMe y
doubleMe x = x + x
doubleSmallNumber x = if x > 100
                        then x
                        else x + x
conanO'Brien = "It's a-me, Conan O'Brien!"

boomBangs xs = [if x < 10 then "BOOM!" else "BANG!" | x <- xs, odd x]

--removeNonUppercase :: [Char] -> [Char]
removeNonUppercase xs = [c | c <- xs, c `elem` ['A'..'Z']]

factorial :: (Integral a) => a -> a
factorial 0 = 1
factorial n = n * factorial (n-1)

head' :: [a] -> a
head' [] = error "Can't call head on an empty list, dummy!"
head' (x:xs) = x

capital :: String -> String
capital [] = "Empty string, whoops!"
capital all@(x:xs) = "The first letter of " ++ all ++ " is " ++ [x]

bmiTell :: (RealFloat a) => a -> a -> String
bmiTell weight height
  | bmi <= skinny = "You're underweight, you emo, you!"
  | bmi <= normal ="You're supposedly normal. Pffft, I bet you're ugly!"
  | bmi <= fat = "You're fat! Lose some weight, fatty!"
  | otherwise = "You're a whale, congratulations!"
  where bmi = weight/height^2
        (skinny,normal,fat) = (18.5, 25.0, 30.0)


max' :: (Ord a) => a -> a -> a
max' a b
  | a < b      = b
  | otherwise  = a

myCompare :: (Ord a) => a -> a -> Ordering
a `myCompare` b
  | a < b     = LT
  | a == b    = EQ
  | otherwise = GT

initials :: String -> String -> String
initials firstname lastname = [f] ++ ". " ++ [l] ++ "."
  where (f:_) = firstname
        (l:_) = lastname

calcBmis :: (RealFloat a) => [(a,a)] -> [a]
calcBmis xs = [bmi w h | (w,h) <- xs]
  where bmi weight height = weight/height^2

cylinder :: (RealFloat a) => a -> a -> a
cylinder r h =
  let sideArea = 2 * pi * r * h
      topArea = pi * r^2
  in sideArea + 2 * topArea

cylinder' :: (RealFloat a) => a -> a -> a
cylinder' r h = sideArea + 2 * topArea
  where sideArea = 2 * pi * r * h
        topArea = pi * r^2

cylinder'' :: (RealFloat a) => a -> a -> a
cylinder'' r h =
  let sideArea = 2 * pi * r * h; topArea = pi * r^2
  in sideArea + 2 * topArea

calcBmis' :: (RealFloat a) => [(a,a)] -> [a]
calcBmis' xs = [bmi | (w,h) <- xs, let bmi = w/h^2, bmi >= 25.0]

head'' :: [a] -> a
head'' xs = case xs of []    -> error "No head for empty lists!"
                       (x:_) -> x

describeList :: [a] -> String
describeList xs  = "The list is " ++ case xs of [] -> "empty."
                                                [x] -> "a singleton list."
                                                xs -> "a longer list."

describeList' :: [a] -> String
describeList' xs = "The list is " ++ what xs
  where what [] = "empty"
        what [x] = "a singleton list"
        what xs = "a longer list"

maximum' :: (Ord a) => [a] -> a
maximum' [] = error "maximum of empty list!"
maximum' [x] = x
maximum' (x:xs)
  | x > maxTail = x
  | otherwise   = maxTail
  where maxTail = maximum' xs

replicate' :: (Integral i, Eq i) => i -> a -> [a]
replicate' 0 x = []
replicate' n x = x:replicate' (n-1) x

take' 0 xs = []
take' n [] = []
take' n (x:xs) = x:(take' (n-1) xs)


elem' :: (Eq a) => a -> [a] -> Bool
elem' a [] = False
elem' a (x:xs) = (a == x) || (elem' a xs)


quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
quicksort [x] = [x]
quicksort (x:xs) =  quicksort [y| y <-xs, y <= x]
                 ++ [x]
                 ++ quicksort [y| y <-xs, x < y]


zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' _ [] _ = []
zipWith' _ _ [] = []
zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys

fib :: (Integral a) => [a]
fib = 0:1:zipWith' (+) fib (tail fib)

fib' :: (Integral a) => [a]
fib' = [fib x| x <- [0..]]
  where fib 0 = 0
        fib 1 = 1
        fib n = fib (n-1) + fib (n-2)

quicksort' :: (Ord a) => [a] -> [a]
quicksort' [] = []
quicksort' (x:xs) =
  let smallerSorted = quicksort' (filter (<=x) xs)
      biggerSorted  = quicksort' (filter (>x)  xs)
  in smallerSorted ++ [x] ++ biggerSorted

largestDivisible :: (Integral a) => a
largestDivisible = head (filter p [100000,99999..])
  where p x = x `mod ` 3829 == 0

s = sum (filter odd [x^2 | x <- [1..99]])
t = sum (takeWhile (<10000) (filter odd (map (^2) [1..])))

chain :: (Integral a) => a -> [a]
chain 1 = [1]
chain n
  | even n = n:chain (n `div` 2)
  | odd n  = n:chain (n*3 + 1)

numLongChains :: Int
numLongChains = length (filter isLong (map chain [1..100]))
  where isLong xs = length xs > 15

numLongChains' :: Int
numLongChains' = length (filter (\xs -> length xs > 15) (map chain [1..100]))

addThree = \x y z -> x + y + z

foldl' :: (a -> b -> a) -> a -> ([b] -> a)
foldl' op v [] = v
foldl' op v (x:xs) = foldl' op (op v x) xs

elem'' :: (Eq a) => a -> [a] -> Bool
elem'' y ys = foldl' (\acc x -> if x == y then True else acc) False ys

map' :: (a -> b) -> [a] -> [b]
map' f = foldr (\x acc -> f x : acc) []

map'' :: (a-> b) -> [a] -> [b]
map'' f = foldl (\acc x -> acc ++ [f x]) []

maxR :: (Ord a) => [a] -> a
maxR = foldr1 (\x acc -> max x acc)

maxL :: (Ord a) => [a] -> a
maxL = foldl1 (\acc x -> max acc x)


foldL :: (a -> b -> a) -> a -> [b] -> a
foldL op v [] = v
foldL op v (x:xs) = foldL op (op v x) xs

foldR :: (b -> a -> a) -> a -> [b] -> a
foldR op v [] = v
foldR op v (x:xs) = op x (foldR op v xs)

reverseR :: [a] -> [a]
reverseR = foldR (\x acc -> acc ++ [x]) []

reverseL :: [a] -> [a]
reverseL = foldL (\acc x -> x:acc) []

productL :: (Num a) => [a] -> a
productL = foldL (*) 1

productR :: (Num a) => [a] -> a
productR = foldR (*) 1

filterL :: (a -> Bool) -> [a] -> [a]
filterL p = foldL (\acc x -> if p x then acc ++ [x] else acc) []

filterR :: (a -> Bool) -> [a] -> [a]
filterR p = foldR (\x acc -> if p x then x:acc else acc) []


headR :: [a] -> Maybe a
headR = foldR (\x acc -> Just x) Nothing

scanL :: (a -> b -> a) -> a -> [b] -> [a]
scanL op v [] = [v]
scanL op v (x:xs) = [v] ++ (scanL op (op v x) xs)

scanR :: (b -> a -> a) -> a -> [b] -> [a]
scanR op v [] = [v]
scanR op v (x:xs) = let ys = scanR op v xs in (op x (head ys)):ys





