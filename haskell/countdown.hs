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

nchoices :: Eq a => Int -> [a] -> [[a]]
nchoices 0 xs = [[]]
nchoices n xs = [(x:ys) | x <- xs, ys <- nchoices (n-1) xs, not (elem x ys)]

choicesDistinct :: Eq a => [a] -> [[a]]
choicesDistinct xs = [ys | n <- [0..(length xs)], ys <- nchoices n xs]

unique :: [a] -> [(Int,a)]
unique [] = []
unique xs = zip [0..((length xs)-1)] xs

extract :: [(Int,a)] -> [a]
extract xs = map snd xs

choices :: Eq a => [a] -> [[a]]
choices xs = map extract (choicesDistinct (unique xs))

values :: Expr -> [Int]
values (Val n) = [n]
values (App _ l r) = values l ++ values r

solution :: Expr -> [Int] -> Int -> Bool
solution e ns n = elem (values e) (choices ns)
                  && eval e == [n]

split :: [a] -> [([a],[a])]
split [] = []
split xs = [(take n xs,drop n xs) | n <- [1..(length(xs)-1)]]

combine :: Expr -> Expr -> [Expr]
combine l r = [App o l r| o <- [Add,Sub,Mul,Div]]

exprs :: [Int] -> [Expr]
exprs [] = []
exprs [n] = [Val n]
exprs ns = [e | (ls,rs) <- split ns
                , l     <- exprs ls
                , r     <- exprs rs
                , e     <- combine l r]

solutions :: [Int] -> Int -> [Expr]
solutions ns n = [e | ns' <- choices ns
                    , e   <- exprs ns'
                    , eval e == [n]]

str :: Expr -> String
str (Val n) =  show n
str (App Add l r) = "(" ++ (str l) ++ "+" ++ (str r) ++ ")"
str (App Sub l r) = "(" ++ (str l) ++ "-" ++ (str r) ++ ")"
str (App Mul l r) = "(" ++ (str l) ++ "*" ++ (str r) ++ ")"
str (App Div l r) = "(" ++ (str l) ++ "/" ++ (str r) ++ ")"



type Result = (Expr,Int)

results :: [Int] -> [Result]
results [] = []
results [n] = [(Val n,n) | n > 0]
results ns = [res | (ls,rs) <- split ns
                  , lx      <- results ls
                  , ry      <- results rs
                  , res     <- combine' lx ry]

combine' :: Result -> Result -> [Result]
combine' (l,x) (r,y) = [(App o l r, apply o x y) | o <- [Add,Sub,Mul,Div]
                                                 , valid' o x y]

solutions' :: [Int] -> Int -> [Expr]
solutions' ns n = [e | ns'   <- choices ns
                     , (e,m) <- results ns'
                     , m == n]


valid' :: Op -> Int -> Int -> Bool
valid' Add x y = (x < y)
valid' Sub x y = (x > y)
valid' Mul x y = (x < y) && x /= 1 && y /= 1
valid' Div x y = (x `mod` y == 0) && y /= 1


