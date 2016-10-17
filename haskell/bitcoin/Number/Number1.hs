{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Number1 (Number1, zero, one, fromBytes, random, toBytes, bitLength) where

import INumber
import Data.Hashable

newtype Number1 = Number1 Integer 
        deriving (Eq, Ord, Num, Real, Enum, Integral, Hashable) 

instance INumber Number1 where
  zero      = zero_
  one       = one_
  fromBytes = fromBytes_
  random    = random_
  toBytes   = toBytes_
  bitLength = bitLength_

instance Show Number1 where 
  show      = show_


zero_ :: Number1
zero_  = Number1 0 

one_  :: Number1
one_   = Number1 1

fromBytes_ :: Sign -> ByteArray -> Number1  -- big endian
fromBytes_  = undefined  -- TODO

random_ :: NumBits -> IO Number1
random_  = undefined     -- TODO

toBytes_ :: Number1 -> NumBits -> ByteArray 
toBytes_  = undefined    -- TODO

bitLength_ :: Number1 -> NumBits
bitLength_  = undefined  -- TODO

show_ :: Number1 -> String
show_ (Number1 x) = (show x)


