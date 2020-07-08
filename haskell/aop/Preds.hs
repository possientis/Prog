{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE OverloadedStrings      #-}

module  Preds
    (   preds1   
    ,   preds
    ,   zero
    ,   suc
    ,   one
    ,   two
    ,   three
    ,   four
    ,   five
    ,   toInt
    ,   fromInt
    ,   sum
    ,   prod
    ,   product
    ,   fact1
    ,   fact
    )   where

import Prelude                  hiding (sum, product)
import Data.Functor.Foldable

data NatF a = Zero | Suc a
    deriving Functor

newtype Nat = Nat { unNat :: Fix NatF }

toInt :: Nat -> Integer
toInt = f . unNat where
    f = cata $ \case
        Zero    -> 0
        Suc n   -> n + 1

fromInt :: Integer -> Nat
fromInt 0 = zero
fromInt n = suc (fromInt (n - 1))


instance Show Nat where
    show = show . toInt

instance Read Nat where
    readsPrec d r = map (\(a,s) -> (fromInt a,s)) $ readsPrec d r

zero :: Nat
zero  = Nat . Fix $ Zero

suc  :: Nat -> Nat
suc n = Nat . Fix . Suc . unNat $ n

one :: Nat 
one = suc zero

two :: Nat 
two = suc one

three :: Nat
three = suc two

four :: Nat
four = suc three

five :: Nat
five = suc four

preds1 :: Nat -> [Nat] 
preds1 = map Nat . f . unNat where
    f = \case
        (Fix Zero)      -> []
        m@(Fix (Suc n)) -> m : f n 

preds :: Nat -> [Nat]
preds = map Nat . fst . f . unNat where
    f = cata $ \case
        Zero        -> ([],Fix (Suc $ Fix Zero))
        Suc (xs,n)  -> (n : xs, Fix (Suc n)) 

sum :: Nat -> Nat -> Nat
sum = f . unNat where
    f = cata $ \case
        Zero    -> id
        Suc g   -> \m -> suc (g m)

prod :: Nat -> Nat -> Nat
prod = f . unNat where
    f = cata $ \case
        Zero    -> const zero
        Suc g   -> \m -> sum m (g m)

product :: [Nat] -> Nat
product = cata $ \case
    Nil           -> one
    (Cons n m)    -> prod n m 

fact1 :: Nat -> Nat 
fact1 = product . preds

fact :: Nat -> Nat
fact = fst . f . unNat where
    f = cata $ \case
        Zero      -> (one, one)
        Suc (x,n) -> (prod x n, suc n)

