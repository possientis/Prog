{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE UndecidableInstances   #-}

import Prelude hiding ((++), length, map, head, tail, concat, toInteger)

data Nat = Zero | Suc Nat

toInteger :: Nat -> Integer
toInteger Zero    = 0
toInteger (Suc n) = 1 + toInteger n

instance Show Nat where
    show = show . toInteger

data Vec (a :: *) (n :: Nat) where
    Nil  :: Vec a Zero
    (:>) :: a -> Vec a n -> Vec a (Suc n)

infixr 5 :>

toList :: Vec a n -> [a]
toList Nil       = []
toList (x :> xs) = x : toList xs

instance Show a => Show (Vec a n) where
    show xs = show $ toList xs

type family (+) (n :: Nat) (m :: Nat) where
    Zero  + m = m
    Suc n + m = Suc (n + m)

type family (*) (n :: Nat) (m :: Nat) where
    Zero  * m = Zero
    Suc n * m = m + (n * m)

(++) :: Vec a n -> Vec a m -> Vec a (n + m)
(++) Nil ys       = ys
(++) (x :> xs) ys = x :> (xs ++ ys)

length :: Vec a n -> Nat
length Nil       = Zero
length (x :> xs) = Suc (length xs)

map :: (a -> b) -> Vec a n -> Vec b n 
map f Nil       = Nil
map f (x :> xs) = f x :> map f xs

head :: Vec a (Suc n) -> a
head (x :> xs) = x

tail :: Vec a (Suc n) -> Vec a n
tail (x :> xs) = xs

concat :: Vec (Vec a m) n -> Vec a (n * m)
concat Nil         = Nil
concat (xs :> xss) = xs ++ concat xss

v1 :: Vec Int (Suc (Suc (Suc Zero)))
v1 = 0 :> 1 :> 2 :> Nil

v2 :: Vec Int (Suc (Suc (Suc Zero)))
v2 = 3 :> 4 :> 5 :> Nil

v3 :: Vec (Vec Int (Suc (Suc (Suc Zero)))) (Suc (Suc Zero))
v3 = v1 :> v2 :> Nil

main :: IO ()
main = do
    print v1
    print v2
    print $ v1 ++ v2
    print $ length (v1 ++ v2)
    print $ map (*2) (v1 ++ v2)
    print $ head v1
    print $ concat v3

