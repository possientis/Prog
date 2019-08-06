{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ExistentialQuantification  #-}

import Data.Kind (Type, Constraint)


data HList (ts :: [Type]) where
    HNil :: HList '[]
    (:#) :: t -> HList ts -> HList (t ': ts)

infixr 5 :#

nil :: HList '[]
nil = HNil

x1 :: HList '[Bool]
x1 = True :# nil

x2 :: HList '[Maybe String, Bool]
x2 = Just "hello" :# x1


data HList_ a 
    = (a ~ '[])     => HNil_
    | forall t ts . (a ~ (t ': ts)) => Cons_ t (HList_ ts)


f :: HList ts -> HList_ ts
f HNil      = HNil_
f (x :# xs) = Cons_ x (f xs)

g :: HList_ ts -> HList ts
g HNil_ = HNil
g (Cons_ x xs) = x :# g xs

hLength :: HList ts -> Int
hLength HNil      = 0
hLength (_ :# xs) = 1 + hLength xs

hLength' :: (Num a) => HList ts -> a
hLength' HNil      = 0
hLength' (_ :# xs) = 1 + hLength' xs

hHead :: HList (t ': ts) -> t
hHead (x :# _) = x


showBool :: HList '[_1, Bool, _2] -> String
showBool (_ :# b :# _ :# HNil) = show b 

x3 :: HList '[Int, Bool, Char]
x3 = 3 :# True :# 'a' :# HNil

{- see more direct definition below
instance Eq (HList '[]) where
    (==) HNil HNil = True

instance (Eq t, Eq (HList ts)) => Eq (HList (t ': ts)) where
    (==) (x :# xs) (y :# ys) = (x == y) && (xs == ys)
-}

instance Show (HList '[]) where
    show HNil = "[]"

instance (Show t, Show (HList ts)) => Show (HList (t ': ts)) where
    show (x :# HNil) = "[" ++ show x ++ "]"
    show (x :# xs)   = "[" ++ show x ++ "," ++ tail (show xs)

{- see more direct definition below (which fails)
instance Ord (HList '[]) where
    (<=) HNil HNil = True

instance (Ord t, Ord (HList ts)) => Ord (HList (t ': ts)) where
    (<=) (x :# xs) (y :# ys) = (x < y) || ((x == y) && (xs <= ys))
-}

type family AllEq (ts :: [Type]) :: Constraint where
    AllEq '[]       = ()
    AllEq (t ': ts) = (Eq t, AllEq ts)

type family All (c :: Type -> Constraint) (ts :: [Type]) :: Constraint where
    All _ '[]       = ()
    All c (t ': ts) = (c t, All c ts)

instance (All Eq ts) => (Eq (HList ts)) where
    (==) HNil HNil           = True
    (==) (x :# xs) (y :# ys) = (x == y) && (xs == ys)

-- fails because cannot deduce (All Eq ts)... so direct route for Eq not that useful
-- Unless you add 'All Eq ts' as constraint
instance (All Ord ts, All Eq ts) => (Ord (HList ts)) where
    (<=) HNil HNil = True
    (<=) (x :# xs) (y :# ys) = (x < y) || ((x == y) && (xs <= ys))



