data Op = Add | Sub | Mul | Div

apply :: Op -> Int -> Int -> Int
apply Add x y = x + y
apply Sub x y = x - y
apply Mul x y = x * y
apply Div x y = x `div` y

valid :: Op -> Int -> Int -> Bool
valid Add _ _ = True
valid Sub x y = (x > y)
valid Mul _ _ = True
valid Div x y = (x `mod` y == 0)

data Expr = Val Int | App Op Expr Expr

myEval :: Expr -> [Int]
myEval (Val n) = [x | x <- [n], x > 0]
myEval (App o l r) = [apply o x y | x <- myEval l
                                  , y <- myEval r
                                  , valid o x y]
eval :: Expr -> [Int]
eval (Val n) = [n | n > 0]
eval (App o l r) = [apply o x y | x <- eval l
                                , y <- eval r
                                , valid o x y]

yourEval :: Expr -> [Int]
yourEval (Val n) = if n > 0 then
                      [n]
                   else
                      []

inList :: Eq a => a -> [a] -> Bool
inList x [] = False
inList x (y:ys) = (x == y) || (inList x ys)

nchoices :: Eq a => Int -> [a] -> [[a]]
nchoices 0 xs = [[]]
nchoices n xs = [(x:ys) | x <- xs, ys <- nchoices (n-1) xs, not (inList x ys)]

choices :: Eq a => [a] -> [[a]]
choices xs = [ys : n <- [0..(length xs)], ys <- nchoices n xs]



