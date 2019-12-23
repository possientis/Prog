{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module  Optics.Nat
    (   Nat         (..)
    )   where

data Nat = Z | S Nat
    deriving (Eq)

instance Show Nat where
    show = show . fromNat

fromNat :: Nat -> Integer
fromNat Z = 0
fromNat (S n) = 1 + fromNat n
