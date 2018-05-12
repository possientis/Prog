{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

data Tuple a where
    MkTuple :: forall a . Int -> Char -> a -> Tuple a


x :: Tuple Char
x = MkTuple 23 'a' 'b'

y :: Tuple Double
y = MkTuple 23 'a' 2


type family Tuple' a where
    Tuple' a = (Int, Char, a)

x' :: Tuple' Char
x' = (23,'a','b')


data Ex a where
    MkEx :: forall a b . b -> a -> Ex a


z :: Ex Int
z = MkEx "Test" 34


data Either' :: * -> * -> * where
    Left' :: forall a b . a -> Either' a b
    Right' :: forall a b. b -> Either' a b

t :: Either'  Int Double
t = Left' 34

data Sum a b = First a | Snd b

data Nat = Zero | Succ Nat

data Vec :: * -> Nat -> * where
    VNil  :: forall a . Vec a 'Zero
    VCons :: forall a n . a -> Vec a n -> Vec a ('Succ n)

plus :: Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

{-
append :: Vec a n -> Vec a m -> Vec a (plus n m)
append VNil ys = ys
append (VCons x xs) ys = VCons x (append xs ys) 
-}
