{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Number2 (Number2, zero, one, fromBytes, random, toBytes, bitLength) where

import INumber
import Data.Hashable

newtype Number2 = Number2 Integer 
        deriving (Eq, Ord, Num, Real, Enum, Integral, Hashable) 

instance INumber Number2 where
  zero      = zero_
  one       = one_
  fromBytes = fromBytes_
  random    = random_
  toBytes   = toBytes_
  bitLength = bitLength_

instance Show Number2 where 
  show      = show_


zero_ :: Number2
zero_  = Number2 0 

one_  :: Number2
one_   = Number2 1

fromBytes_ :: Sign -> ByteArray -> Number2  -- big endian
fromBytes_  = undefined  -- TODO

random_ :: NumBits -> IO Number2
random_  = undefined     -- TODO

toBytes_ :: Number2 -> NumBits -> ByteArray 
toBytes_  = undefined    -- TODO

bitLength_ :: Number2 -> NumBits
bitLength_  = undefined  -- TODO

show_ :: Number2 -> String
show_ (Number2 x) = (show x)


