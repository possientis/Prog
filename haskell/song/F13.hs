module  F13
    (   F13 (..)
    )   where

import Prelude as P
import Test.QuickCheck

import Field
import HasPrime
import IsInteger
import PrimeField

newtype F13 = F13 { unF13 :: Integer }

instance Show F13 where
    show = show . unF13

instance HasPrime F13 where
    prime _ = 13 

instance IsInteger F13 where
    toInteger   = unF13
    fromInteger = F13

instance Field F13 where
    (+)  = fieldAdd
    (*)  = fieldMul
    neg  = fieldNeg
    inv  = fieldInv
    zero = fieldZero
    one  = fieldOne

instance Arbitrary F13 where
    arbitrary = fieldArbitrary

instance Eq F13 where 
    (==) = fieldEq

