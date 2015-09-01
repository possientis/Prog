add x y   = x + y
zeroto :: Int -> [Int]
zeroto n = [0..n]
f :: Int -> Int -> Int
f = \x -> \y -> x + y
mult :: Int -> Int -> Int -> Int
mult x y z = x*y*z
myLength :: [a] -> Int
myLength [] = 0
myLength x = 1 + myLength (tail x)
mySum :: Num a => [a] -> a
mySum [] = 0
mySum x = (head x) + mySum (tail x)
second xs = head (tail xs)
swap (x,y) = (y,x)
pair x y = (x,y)
double x = 2*x
palindrome xs = reverse xs == xs
twice f x = f (f x)
