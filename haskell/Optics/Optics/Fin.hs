{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

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

instance (Equal n a) => Eq (Fin n -> a) where
    (==) f g = equal f g

class Equal n a where
    equal :: (Fin n -> a) -> (Fin n -> a) -> Bool

instance Equal 'Z a where
    equal _ _ = True

instance (Eq a, Equal n a) => Equal ('S n) a where
    equal f g = (f FZ == g FZ) 
              && equal (\n -> f (FS n)) (\n -> g (FS n))

class ToList n a where
    toList :: (Fin n -> a) -> [a]
 
instance ToList 'Z a where
    toList _ = []

instance (ToList n a) => ToList ('S n) a where
    toList f = f FZ : toList (\n -> f (FS n))

instance (ToList n a, Show a) => Show (Fin n -> a) where
    show = show . toList
