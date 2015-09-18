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
  | weight/height^2 <= 18.5 = "You're underweight, you emo, you!"
  | weight/height^2 <= 25.0 ="You're supposedly normal. Pffft, I bet you're ugly!"
  | weight/height^2  <= 30.0 = "You're fat! Lose some weight, fatty!"
  | otherwise = "You're a whale, congratulations!"


max' :: (Ord a) => a -> a -> a
max' a b
  | a < b      = b
  | otherwise  = a

myCompare :: (Ord a) => a -> a -> Ordering
a `myCompare` b
  | a < b     = LT
  | a == b    = EQ
  | otherwise = GT


