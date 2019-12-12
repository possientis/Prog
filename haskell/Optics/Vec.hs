{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}

module  Optics.Vec
    (   Vec (..)
    )   where

import Data.Kind
import Optics.Nat

data Vec (n :: Nat) (a :: Type) :: Type where
    Nil  :: forall (a :: Type) . Vec 'Z a
    Cons :: forall (a :: Type) (n :: Nat) . a -> Vec n a -> Vec ('S n) a

instance (Eq a) => Eq (Vec n a) where
    (==) Nil Nil = True
    (==) (Cons x xs) (Cons y ys) = (x == y) && xs == ys


