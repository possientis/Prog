{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE FlexibleContexts       #-}

module  GenericEq
    (   GEq     (..)
    ,   Foo     (..)
    )   where


import Data.Kind
import GHC.Generics

class GEq (a :: Type -> Type) where
    geq :: a x -> a x -> Bool

-- U1 :: Type -> Type is meant to represent ()
instance GEq U1 where   
    geq U1 U1 = True

-- V1 :: Type -> Type is meant to represent Void
instance GEq V1 where
    geq _ _   = True 

instance Eq a => GEq (K1 _1 a) where
    geq (K1 x) (K1 y) = x == y

instance (GEq a, GEq b) => GEq (a :+: b) where
    geq (L1 x) (L1 y) = geq x y
    geq (R1 x) (R1 y) = geq x y
    geq _ _           = False

instance (GEq a, GEq b) => GEq (a :*: b) where
    geq (x1 :*: y1) (x2 :*: y2) = geq x1 x2 && geq y1 y2

instance GEq a => GEq (M1 _x _y a) where
    geq (M1 x) (M1 y) = geq x y

genericEq :: (Generic a, GEq (Rep a)) => a -> a -> Bool
genericEq x y = geq (from x) (from y)

data Foo a b c
    = F0
    | F1 a
    | F2 b c
    deriving (Generic)

instance (Eq a, Eq b, Eq c) => Eq (Foo a b c) where
    (==) = genericEq



main :: IO ()
main = do
    print $ genericEq True  True
    print $ genericEq True  False
    print $ genericEq False True
    print $ genericEq False False
    print $ genericEq "hello" "hello"
    print $ genericEq "hello" "Hello"



