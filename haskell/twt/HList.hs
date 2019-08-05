{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ExistentialQuantification  #-}

import Data.Kind (Constraint, Type)


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
