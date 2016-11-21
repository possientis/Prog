{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Number2 
  ( Number2
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
import Rand
import Data.Hashable (Hashable, hash)
import Data.Word (Word8)
import Data.Bits (shiftR, shiftL, testBit, (.&.))
import Data.ByteString hiding (putStrLn, length)
import Prelude hiding (all, head, tail)


newtype Number2 = Number2 Integer 
        deriving (Eq, Ord, Num, Real, Enum, Integral, Hashable) 

instance INumber Number2 where
  zero      = zero_
  one       = one_
  fromBytes = fromBytes_
  random    = random_
  toBytes   = toBytes_
  sign      = sign_
  bitLength = bitLength_

instance Show Number2 where 
  show      = show_

show_ :: Number2 -> String
show_ (Number2 x) = (show x)

zero_ :: Number2
zero_  = Number2 0 

one_  :: Number2
one_   = Number2 1

sign_ :: Number2 -> Int
sign_ (Number2 x)
  | x == 0  = 0
  | x <= 0  = -1
  | x >= 0  = 1


fromBytes_ :: Sign -> ByteString -> Rand Number2  -- big endian
fromBytes_  (Sign sig) bytes
  | sig == 1    = return $ Number2 x
  | sig == (-1) = return  $ Number2 (-x) 
  | sig == 0    = 
      if all (== 0) bytes
        then return $ Number2 0
        else throw $
          randException "InvalidArgument" "fromBytes: inconsistent arguments"
  | otherwise   = throw $ 
    randException "InvalidArgument" "fromBytes: illegal sign argument"
  where 
    x     = go 0 list
    list  = unpack bytes
    go :: Integer -> [Word8] -> Integer 
    go acc [] = acc
    go acc (b:bs) = go ((shiftL acc 8) + toInteger b) bs 

-- returns unsigned random number of requested size in bits
random_ :: NumBits -> Rand Number2
random_ n = do
  bytes <- randomBytes_ n 
  fromBytes (Sign 1) bytes

-- returns unsigned random number as big endian ByteArray
-- Essentially generates random bytes and subsequently set
-- the appropriate number of leading bits to 0 so as to 
-- ensure the final ByteArray has the right bit size.
randomBytes_ :: NumBits -> Rand ByteString
randomBytes_ (NumBits n) = 
  let len = div (n + 7) 8 in    -- number of bytes required
    if len == 0 
      then return empty         -- empty ByteString
      else do
        bytes <- getRandomBytes len
        let lead = head bytes
        let diff = len * 8 - n  -- number of leading bits set to 0 
        let front = truncate_ diff lead
        return $ cons front (tail bytes)

-- returns byte with n leading bits set to 0
truncate_ :: Int -> Word8 -> Word8  
truncate_ n w = go 0x7f n w where
  go :: Word8 -> Int -> Word8 -> Word8
  go mask n w = 
    if n == 0
      then w
      else go (mask `shiftR` 1) (n - 1) (w .&. mask)
    

testTruncate :: IO ()
testTruncate = do
  putStrLn $ show (truncate_ 0 0xff)
  putStrLn $ show (truncate_ 1 0xff)
  putStrLn $ show (truncate_ 2 0xff)
  putStrLn $ show (truncate_ 3 0xff)
  putStrLn $ show (truncate_ 4 0xff)
  putStrLn $ show (truncate_ 5 0xff)
  putStrLn $ show (truncate_ 6 0xff)
  putStrLn $ show (truncate_ 7 0xff)
  putStrLn $ show (truncate_ 8 0xff)
     

toBytes_ :: Number2 -> NumBytes -> Rand ByteString
toBytes_  (Number2 x) (NumBytes num)
  | x < 0     = toBytes (Number2 $ -x) (NumBytes num)
  | len < 0   = throw $ 
    randException "InvalidArgument" "toBytes: NumBytes argument is too small"
  | otherwise = return $ pack $ padding len list 
  where
    list = (unroll x)
    len = num - length list


-- number of bits required to encode magnitude of number
bitLength_ :: Number2 -> NumBits
bitLength_  (Number2 x)
  | x < 0     = bitLength (Number2 $ -x)
  | len == 0  = NumBits 0
  | otherwise = NumBits (len * 8 - adjust)
  where
    list    = unroll x
    len     = length list
    byte    = list !! 0
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


