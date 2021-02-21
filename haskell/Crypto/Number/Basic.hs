module  Number.Basic
    (   sqrti
    ,   gcde
    ,   areEven
    ,   log2
    ,   numBits
    ,   numBytes
    ,   asPowerOf2AndOdd
    )   where

import Data.Bits

import Number.GMP

-- | cut and paste from cryptonite
-- | @sqrti@ returns two integers @(l,b)@ so that @l <= sqrt i <= b@.
sqrti :: Integer -> (Integer, Integer)
sqrti i
    | i < 0     = error "cannot compute negative square root"
    | i == 0    = (0,0)
    | i == 1    = (1,1)
    | i == 2    = (1,2)
    | otherwise = loop x0
    where
        nbdigits = length $ show i
        x0n = (if even nbdigits then nbdigits - 2 else nbdigits - 1) `div` 2
        x0  = if even nbdigits then 2 * 10 ^ x0n else 6 * 10 ^ x0n
        loop x = case compare (sq x) i of
            LT -> iterUp x
            EQ -> (x, x)
            GT -> iterDown x
        iterUp lb = if sq ub >= i then iter lb ub else iterUp ub
            where ub = lb * 2
        iterDown ub = if sq lb >= i then iterDown lb else iter lb ub
            where lb = ub `div` 2
        iter lb ub
             | lb == ub   = (lb, ub)
             | lb+1 == ub = (lb, ub)
             | otherwise  =
                 let d = (ub - lb) `div` 2 in
                 if sq (lb + d) >= i
                     then iter lb (ub-d)
                     else iter (lb+d) ub
        sq a = a * a

-- | gcde a b = (x, y, gcd a b) where ax + by = gcd a b
gcde :: Integer -> Integer -> (Integer, Integer, Integer)
gcde = gmpGcde

-- | Check if a list of integer are all even
areEven :: [Integer] -> Bool
areEven = and . map even

log2 :: Integer -> Int
log2 = gmpLog2
{-# INLINE log2 #-}

numBits :: Integer -> Int
numBits = gmpSizeInBits

numBytes :: Integer -> Int
numBytes = gmpSizeInBytes


-- | Express an integer as an odd number and a power of 2
-- | asPowerOf2AndOdd a = (k,n) where  a = (2^k)*n and n odd
asPowerOf2AndOdd :: Integer -> (Int, Integer)
asPowerOf2AndOdd a
    | a == 0       = (0, 0)
    | odd a        = (0, a)
    | a < 0        = let (e, a1) = asPowerOf2AndOdd $ abs a in (e, -a1)
    | isPowerOf2 a = (log2 a, 1)
    | otherwise    = loop a 0
        where      
          isPowerOf2 n = (n /= 0) && ((n .&. (n - 1)) == 0)
          loop n pw = if n `mod` 2 == 0 then loop (n `div` 2) (pw + 1)
                      else (pw, n)
