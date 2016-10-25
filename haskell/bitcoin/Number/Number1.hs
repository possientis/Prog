{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Number1 (  Number1, 
                  NumBytes(..),
                  zero, 
                  one, 
                  fromBytes, 
                  random, 
                  toBytes, 
                  bitLength, 
                  sign,
                  hash
  ) where

import INumber
import Data.Hashable (Hashable, hash)
import Data.Word (Word8)
import Data.Bits (shiftR)
import qualified Data.ByteString.Lazy as L


newtype Number1 = Number1 Integer 
        deriving (Eq, Ord, Num, Real, Enum, Integral, Hashable) 

instance INumber Number1 where
  zero      = zero_
  one       = one_
  fromBytes = fromBytes_
  random    = random_
  toBytes   = toBytes_
  sign      = sign_
  bitLength = bitLength_

instance Show Number1 where 
  show      = show_

show_ :: Number1 -> String
show_ (Number1 x) = (show x)

zero_ :: Number1
zero_  = Number1 0 

one_  :: Number1
one_   = Number1 1

sign_ :: Number1 -> Int
sign_ (Number1 x)
  | x == 0  = 0
  | x <= 0  = -1
  | x >= 0  = 1


fromBytes_ :: Sign -> ByteArray -> Number1  -- big endian
fromBytes_  = undefined  -- TODO

random_ :: NumBits -> IO Number1
random_  = undefined     -- TODO

toBytes_ :: Number1 -> NumBytes -> ByteArray 
toBytes_  (Number1 x) _ = L.pack (unroll x)

bitLength_ :: Number1 -> NumBits
bitLength_  = undefined  -- TODO

unroll :: Integer -> [Word8]
unroll = unfold step where
  step 0 = Nothing
  step i = Just (fromInteger i, i `shiftR` 8) 

unfold :: (b -> Maybe (a,b)) -> b -> [a]
unfold step b = go b [] where
  go b acc =
    case step b of
      Nothing     -> acc
      Just (a,b') -> go b' (a:acc) -- tail recursive






