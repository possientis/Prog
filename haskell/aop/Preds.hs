{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module  Preds
    (   preds1   
    ,   preds
    ,   zero
    ,   suc
    ,   toInt
    ,   fromInt
    )   where

import Data.Functor.Foldable

data NatF a = Zero | Suc a
    deriving Functor

newtype Nat = Nat { unNat :: Fix NatF }

toInt :: Nat -> Int
toInt = f . unNat where
    f = cata $ \case
        Zero    -> 0
        Suc n   -> n + 1

fromInt :: Int -> Nat
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
