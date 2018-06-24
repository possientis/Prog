{-# LANGUAGE GADTs #-}

data Expr' a = IntLit' Int                          -- has type Expr' a
             | BoolLit' Bool                        -- has type Expr' a
             | If' (Expr' Bool) (Expr' a) (Expr' a)



data Expr a where
    IntLit  :: Int  -> Expr Int     
    BoolLit :: Bool -> Expr Bool
    If      :: Expr Bool -> Expr a -> Expr a -> Expr a 


crazyEval :: Expr a -> a
crazyEval (IntLit x) = 
    -- here we can use '(+)' because x :: Int
    x + 1
crazyEval (BoolLit b) =
    -- here we can use 'not' because b :: Bool
    not b
crazyEval (If b thn els) =
    -- because b :: Expr Bool, we can use crazyEval b :: Bool
    -- also because thn :: Expr a and els :: Expr a we can pass
    -- either to the recursive call to'crazyEval' and get an a back
    crazyEval $ if crazyEval b then thn else els




