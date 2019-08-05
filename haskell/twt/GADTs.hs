{-# LANGUAGE GADTs   #-}

five :: Int
five = 5

five_ :: (a ~ Int) => a
five_ = 5


data Expr a where
    LitInt  :: Int -> Expr Int
    LitBool :: Bool -> Expr Bool
    Add     :: Expr Int -> Expr Int -> Expr Int
    Not     :: Expr Bool -> Expr Bool
    If      :: Expr Bool -> Expr a -> Expr a -> Expr a

data Expr_ a 
    = (a ~ Int)  => LitInt_  Int
    | (a ~ Bool) => LitBool_ Bool
    | (a ~ Int)  => Add_ (Expr_ Int) (Expr_ Int)
    | (a ~ Bool) => Not_ (Expr_ Bool)
    |               If_ (Expr_ Bool) (Expr_ a) (Expr_ a)

f :: Expr a -> Expr_ a
f (LitInt n)    = LitInt_ n
f (LitBool b)   = LitBool_ b 
f (Add e1 e2)   = Add_ (f e1) (f e2)
f (Not e1)      = Not_ (f e1)
f (If b1 e1 e2) = If_  (f b1) (f e1) (f e2) 

g :: Expr_ a -> Expr a
g (LitInt_ n)   = LitInt n
g (LitBool_ b)  = LitBool b
g (Add_ e1 e2)  = Add (g e1) (g e2)
g (Not_ e1)     = Not (g e1)
g (If_ b1 e1 e2)= If (g b1) (g e1) (g e2)

eval :: Expr a -> a
eval (LitInt n)     = n
eval (LitBool b)    = b
eval (Add e1 e2)    = eval e1 + eval e2
eval (Not e1)       = not $ eval e1
eval (If b1 e1 e2)  = if eval b1 then eval e1 else eval e2

x1 :: Expr Int
x1 = If (LitBool False) (LitInt 1) (Add (LitInt 5) (LitInt 13))

x2 :: Expr Bool
x2 = Not (LitBool True)

