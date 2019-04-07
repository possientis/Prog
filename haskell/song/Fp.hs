module  Fp
    (   Fp (..)
    )   where

-- Prime field underling the elliptic curve seck256k1

import Test.QuickCheck

import Field
import HasPrime
import IsInteger
import PrimeField


newtype Fp = Fp { unFp :: Integer }

instance Show Fp where
    show = show . unFp

instance HasPrime Fp where
    prime _ = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

instance IsInteger Fp where
    toInteger   = unFp
    fromInteger = Fp

instance Field Fp where
    (+)  = fieldAdd
    (*)  = fieldMul
    neg  = fieldNeg
    inv  = fieldInv
    zero = fieldZero
    one  = fieldOne

instance Arbitrary Fp where
    arbitrary = fieldArbitrary

instance Eq Fp where 
    (==) = fieldEq

