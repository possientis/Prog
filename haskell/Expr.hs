data Expr a
    = Val a
    | Add (Expr a) (Expr a)
    | Sub (Expr a) (Expr a)
    | Mul (Expr a) (Expr a)
    | Div (Expr a) (Expr a)

eval :: (Integral a) => Expr a -> a
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y


instance (Num a) => Num (Expr a) where
    (+) = Add
    (*) = Mul
    (-) = Sub
    abs = undefined
    signum = undefined
    fromInteger = Val . fromInteger


x1 :: Expr Integer
x1 = 6 + 3 * 12

main :: IO ()
main = do
    print $ eval x1


