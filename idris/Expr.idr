data Expr a = Val a
            | Add (Expr a) (Expr a)
            | Sub (Expr a) (Expr a)
            | Mul (Expr a) (Expr a) 
            | Div (Expr a) (Expr a)

eval : (Neg a, Integral a) => Expr a -> a
eval (Val x)   = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y


Num a => Num (Expr a) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger



x : Expr Integer
x = 6 + 3 * 12


main : IO ()
main = do
  printLn $ eval x
