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

decomp :: [a] -> [([a],[a])]
decomp [] = [([],[])]
decomp (x:xs) = [(x:u,v) | (u,v)  <- decomp xs] ++ [([],x:xs)]

choices :: [a] -> [[a]]
choices [] = [[]]
choices (x:xs) =  [ys | ys <- choices xs]

