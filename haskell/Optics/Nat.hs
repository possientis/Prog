{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module  Optics.Nat
    (   Nat         (..)
    ,   SNat        (..)
    ,   KnownNat    (..)
    )   where


data Nat = Z | S Nat

data SNat = SZ | SS SNat

class KnownNat (n :: Nat) where
    value :: SNat

instance KnownNat 'Z where
    value = SZ

instance (KnownNat n) => KnownNat ('S n) where
    value = SS (value @ n)
