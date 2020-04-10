{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeSynonymInstances   #-}


data Fix f = Fix { unFix :: f (Fix f) } 

data NatF a = Zero | Suc a
    deriving Functor

type Nat = Fix NatF

cata :: Functor f => (f a -> a) -> Fix f -> a
cata g = g . fmap (cata g) . unFix     

natRecWeak :: a -> (a -> a) -> Nat -> a
natRecWeak x s = cata $ \case
    Zero    -> x
    Suc a   -> s a  

natRec :: a -> (Nat -> a -> a) -> Nat -> a
natRec x s (Fix n) = case n of
    Zero    -> x
    Suc m   -> s m (natRec x s m)

toInt :: Nat -> Int
toInt = natRec 0 (const (+1))

instance Show Nat where
    show = show . toInt

fromInt :: Int -> Nat
fromInt 0 = Fix Zero
fromInt n = Fix (Suc (fromInt (n - 1)))

zero :: Nat 
zero = Fix Zero

one :: Nat
one = Fix (Suc zero)

suc :: Nat -> Nat
suc = natRec one (const $ Fix . Suc)

plus1 :: Nat -> Nat -> Nat 
plus1 n = natRec n (const suc)
