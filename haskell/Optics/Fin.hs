{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}

module  Optics.Fin
    (   Fin (..)
    ,   absurd
    )   where

import Data.Kind
import Optics.Nat

data Fin (n :: Nat) :: Type where
    FZ :: forall (n :: Nat) . Fin ('S n)
    FS :: forall (n :: Nat) . Fin n -> Fin ('S n)

absurd :: forall (a :: Type) . Fin 'Z -> a
absurd x = case x of {}

