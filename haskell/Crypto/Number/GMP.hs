{-# LANGUAGE MagicHash     #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE BangPatterns  #-}

module  Number.GMP
    (   gmpGcde
    ,   gmpLog2
    ,   gmpPowModSecInteger
    ,   gmpPowModInteger
    ,   gmpInverse
    ,   gmpNextPrime
    ,   gmpTestPrimeMillerRabbin
    ,   gmpSizeInBytes
    ,   gmpSizeInBits
    ,   gmpExportInteger
    ,   gmpExportIntegerLE
    ,   gmpImportInteger
    ,   gmpImportIntegerLE
    )   where

import GHC.Ptr
import GHC.Base
import GHC.Integer.Logarithms
import GHC.Integer.GMP.Internals

import Data.Word

-- | e.g. gmpGcde 250 100 = (1,-2,50) since 50 = 1*250 + (-2)*100
gmpGcde :: Integer -> Integer -> (Integer, Integer, Integer)
gmpGcde a b = (s, t, g)
    where 
        (# g, s #) = gcdExtInteger a b
        t = (g - s * a) `div` b

-- | e.g. gmpLog2 0 = 0, gmpLog2 1 = 0, gmpLog2 2 = 1, gmpLog2 3 = 1, gmpLog2 4 = 2
gmpLog2 :: Integer -> Int
gmpLog2 0 = 0
gmpLog2 x = I# (integerLog2# x)

-- | Power modulo, extra security to resist timing attacks
gmpPowModSecInteger :: Integer -> Integer -> Integer -> Integer
gmpPowModSecInteger b e m = powModSecInteger b e m

-- | Power modulo, no extra security
gmpPowModInteger :: Integer -> Integer -> Integer -> Integer
gmpPowModInteger b e m = powModInteger b e m


-- | Inverse modulo  
gmpInverse :: Integer -> Integer -> Maybe Integer
gmpInverse g m 
    | r == 0    = Nothing
    | otherwise = Just r
    where
        r = recipModInteger g m

-- | e.g. gmpNextPrime 2 = 3
gmpNextPrime :: Integer -> Integer
gmpNextPrime = nextPrimeInteger

-- | Reasonable values of 'tries' are between 15 and 50
gmpTestPrimeMillerRabbin :: Int -> Integer -> Bool
gmpTestPrimeMillerRabbin (I# tries) !n = case testPrimeInteger n tries of
    0#  -> False
    _   -> True

-- | Return the size in bytes of an (unsigned) integer
gmpSizeInBytes :: Integer -> Int
gmpSizeInBytes n = I# (word2Int# (sizeInBaseInteger n 256#))

-- | Return the size in bits of an (unsigned) integer
gmpSizeInBits :: Integer -> Int
gmpSizeInBits n = I# (word2Int# (sizeInBaseInteger n 2#))

-- | Export an integer to a memory (big-endian)
gmpExportInteger :: Integer -> Ptr Word8 -> IO ()
gmpExportInteger n (Ptr addr) = do
    _ <- exportIntegerToAddr n addr 1#
    return ()

-- | Export an integer to a memory (little-endian)
gmpExportIntegerLE :: Integer -> Ptr Word8 -> IO ()
gmpExportIntegerLE n (Ptr addr) = do
    _ <- exportIntegerToAddr n addr 0#
    return ()

-- | Import an integer from a memory (big-endian)
gmpImportInteger :: Int -> Ptr Word8 -> IO Integer
gmpImportInteger (I# n) (Ptr addr) = importIntegerFromAddr addr (int2Word# n) 1#

-- | Import an integer from a memory (little-endian)
gmpImportIntegerLE :: Int -> Ptr Word8 -> IO Integer
gmpImportIntegerLE (I# n) (Ptr addr) = importIntegerFromAddr addr (int2Word# n) 0#

