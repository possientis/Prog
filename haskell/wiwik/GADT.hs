{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
--{-# LANGUAGE KindSignatures #-}

-- Using constraints
data Exp a 
    = (a ~ Int)     => LitInt a
    | (a ~ Bool)    => LitBool a
    | forall b. (b ~ Bool) => If (Exp b) (Exp a) (Exp a)


-- Using GADTs
data Exp' a where
    LitInt'  :: Int -> Exp' Int
    LitBool' :: Bool -> Exp' Bool
    If'      :: Exp' Bool -> Exp' a -> Exp' a -> Exp' a



eval :: Exp a -> a
eval e = case e of
    LitInt i    -> i
    LitBool b   -> b
    If b e1 e2  -> if eval b then eval e1 else eval e2

{--
data T :: * -> * where
    T1 :: Int -> T Int
    T2 :: T a

f (T1 n) = [n]
f T2     = []
--}
