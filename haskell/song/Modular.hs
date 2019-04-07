{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module  Modular
    (   Mod     (..)
    )   where

import Data.Proxy
import GHC.TypeLits
import Test.QuickCheck

import Field
import HasPrime
import IsInteger
import PrimeField

newtype Mod (n :: Nat) = Mod { unMod :: Integer }

instance Show (Mod n) where
    show = show . unMod

instance (KnownNat n) => HasPrime (Mod n) where
    prime _ = natVal (Proxy :: Proxy n)

instance IsInteger (Mod n) where
    toInteger (Mod x) = x
    fromInteger       = Mod

instance (KnownNat n) => Field (Mod n) where
    (+)  = fieldAdd
    (*)  = fieldMul
    neg  = fieldNeg
    inv  = fieldInv
    zero = fieldZero
    one  = fieldOne

instance Arbitrary (Mod n) where
    arbitrary = fieldArbitrary

instance (KnownNat n) => Eq (Mod n) where
    (==) = fieldEq

