{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Number1 
  ( Number1
  , NumBytes(..)
  , NumBits(..)
  , Sign(..)
  , zero
  , one
  , fromBytes
  , random
  , toBytes
  , bitLength
  , sign
  , hash
  ) where

import INumber
import Data.Hashable (Hashable, hash)
import Data.Word (Word8)
import Data.Bits (shiftR, shiftL, testBit)
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


-- TODO
fromBytes_ :: Sign -> ByteArray -> Maybe Number1  -- big endian
fromBytes_  (Sign sig) bytes
  | sig == 0    = Just $ Number1 0
  | sig == 1    = Just $ Number1 x
  | sig == (-1) = Just $ Number1 (-x) 
  | otherwise   = Nothing
  where 
    x     = go 0 list
    list  = L.unpack bytes
    go :: Integer -> [Word8] -> Integer 
    go acc [] = acc
    go acc (b:bs) = go ((shiftL acc 8) + toInteger b) bs 


random_ :: NumBits -> IO Number1
random_  = undefined     -- TODO

toBytes_ :: Number1 -> NumBytes -> Maybe ByteArray 
toBytes_  (Number1 x) (NumBytes num)
  | x < 0     = toBytes (Number1 $ -x) (NumBytes num)
  | len < 0   = Nothing
  | otherwise = Just $ L.pack $ padding len list 
  where
    list = (unroll x)
    len = num - length list


-- number of bits required to encode magnitude of number
bitLength_ :: Number1 -> NumBits
bitLength_  (Number1 x)
  | x < 0     = bitLength (Number1 $ -x)
  | len == 0  = NumBits 0
  | otherwise = NumBits (len * 8 - adjust)
  where
    list    = unroll x
    len     = length list
    byte    = head list
    adjust  = leadBitCount byte
  

-- returns the number of leading bits equal to 0
leadBitCount :: Word8 -> Int
leadBitCount byte = go 0 7 byte where
  go count position byte 
    | position < 0          = count
    | testBit byte position = count
    | otherwise             = go (count + 1) (position - 1) byte 
    

-- adding a certain number of leading 0x00 bytes
padding :: Int -> [Word8] -> [Word8]
padding num list
  | num <= 0    = list
  | otherwise   = padding (num - 1) ((0x00):list)

-- applying unfold to convert Integer to list of bytes in big-endian format
unroll :: Integer -> [Word8]
unroll = unfold step where
  step 0 = Nothing
  step i = Just (fromInteger i, i `shiftR` 8) 

-- our own version of unfold, so as to end up with big-endian 
unfold :: (b -> Maybe (a,b)) -> b -> [a]
unfold step b = go b [] where
  go b acc =
    case step b of
      Nothing     -> acc
      Just (a,b') -> go b' (a:acc) -- tail recursive


