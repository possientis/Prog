{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}

module  Optics.Vec
    (   Vec (..)
    ,   toList
    ,   nth
    ,   head
    ,   append
    ,   makeEven
    ,   vtake
    ,   vtake2
    ,   replicate1
    )   where

import Prelude      hiding (head)
import Data.Kind

import Optics.Nat
import Optics.Leq
import Optics.Plus
import Optics.IsEven
import Optics.Singleton

data Vec (n :: Nat) (a :: Type) :: Type where
    Nil  :: forall (a :: Type) . Vec 'Z a
    Cons :: forall (a :: Type) (n :: Nat) . a -> Vec n a -> Vec ('S n) a

instance (Eq a) => Eq (Vec n a) where
    (==) Nil Nil = True
    (==) (Cons x xs) (Cons y ys) = (x == y) && xs == ys

instance (Show a) => (Show (Vec n a)) where
    show = show . toList

toList :: Vec n a -> [a]
toList Nil = []
toList (Cons x xs) = x : toList xs


nth :: forall (m :: Nat) (n :: Nat) (a :: Type)
     . (m :< n) ~ 'True
    => SNat m 
    -> Vec n a
    -> a
-- nth SZ      Nil         = error "out of bound" : does not typecheck
nth SZ      (Cons x _)  = x
nth (SS n)  (Cons _ xs) = nth n xs 

head :: Vec ('S n) a -> a
head (Cons x _) = x

append :: Vec n a -> Vec m a -> Vec (Plus n m) a
append  Nil        ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

makeEven :: SNat n -> Vec n a -> Vec (NextEven n) a
makeEven n xs = case sIsEven n of
    STrue  -> xs
    SFalse -> case xs of
        Cons x _ -> Cons x xs

vtake :: Nat -> Vec n a -> [a]
vtake Z _ = []
vtake (S _) Nil = error "Index out of bound"
vtake (S n) (Cons x xs) = x : vtake n xs 

{- works but creates warning for redundant constraint.
vtake1 :: (m :< n) ~ 'True
       => SNat m 
       -> Vec n a
       -> [a]
vtake1 m vec = vtake (fromSing m) vec
-}

replicate1 :: SNat n -> a -> Vec n a
replicate1 SZ _ = Nil
replicate1 (SS n) x = Cons x (replicate1 n x)

vtake2 :: (m :< n) ~ 'True
       => SNat m 
       -> Vec n a
       -> Vec m a
vtake2 SZ _ = Nil
vtake2 (SS n) (Cons x xs) = Cons x (vtake2 n xs) 

