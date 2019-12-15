{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}

module  Optics.Vec
    (   Vec (..)
    ,   main
    ,   nth
    ,   head
    ,   append
    )   where

import Prelude      hiding (head)
import Data.Kind
import Optics.Nat

data Vec (n :: Nat) (a :: Type) :: Type where
    Nil  :: forall (a :: Type) . Vec 'Z a
    Cons :: forall (a :: Type) (n :: Nat) . a -> Vec n a -> Vec ('S n) a

instance (Eq a) => Eq (Vec n a) where
    (==) Nil Nil = True
    (==) (Cons x xs) (Cons y ys) = (x == y) && xs == ys

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

vec1 :: Vec ('S ('S ('S 'Z))) Int
vec1 = Cons 0 (Cons 1 (Cons 2 Nil))

main :: IO ()
main = do
    print $ head vec1
    print $ nth SZ vec1
    print $ nth (SS SZ) vec1
    print $ nth (SS (SS SZ)) vec1
--    print $ nth (SS (SS (SS SZ))) vec1 : does not typecheck

