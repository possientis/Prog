module  F13
    (   F13 (..)
    )   where

import Field
import IsInteger
import HasPrime
import PrimeField

newtype F13 = F13 { unF13 :: Integer} deriving (Eq)

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

    

