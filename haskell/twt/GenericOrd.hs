{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE FlexibleContexts       #-}

import Data.Kind
import GHC.Generics
import GenericEq

class GEq a => GOrd (a :: Type -> Type) where
    gle :: a x -> a x -> Bool

-- U1 :: Type -> Type is meant to represent ()
instance GOrd U1 where   
    gle U1 U1 = True

-- V1 :: Type -> Type is meant to represent Void
instance GOrd V1 where
    gle _ _   = True 

instance Ord a => GOrd (K1 _1 a) where
    gle (K1 x) (K1 y) = x <= y

instance (GOrd a, GOrd b) => GOrd (a :+: b) where
    gle (L1 x) (L1 y) = gle x y
    gle (R1 x) (R1 y) = gle x y
    gle (L1 _) (R1 _) = True
    gle (R1 _) (L1 _) = False

instance (GOrd a, GOrd b) => GOrd (a :*: b) where
    gle (x1 :*: y1) (x2 :*: y2) = gle x1 x2 || (geq x1 x2 && gle y1 y2)

instance GOrd a => GOrd (M1 _x _y a) where
    gle (M1 x) (M1 y) = gle x y

genericOrd :: (Generic a, GOrd (Rep a)) => a -> a -> Bool
genericOrd x y = gle (from x) (from y)

instance (Ord a, Ord b, Ord c) => Ord (Foo a b c) where
    (<=) = genericOrd



main :: IO ()
main = do
    print $ genericOrd True  True
    print $ genericOrd True  False
    print $ genericOrd False True
    print $ genericOrd False False
    print $ genericOrd "hello" "hello"
    print $ genericOrd "hello" "Hello"



