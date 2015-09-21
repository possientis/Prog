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


