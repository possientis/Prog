module INumber
  ( Sign(..)
  , NumBits(..)
  , NumBytes(..)
  , INumber
  , zero
  , one
  , fromBytes
  , random
  , toBytes
  , sign
  , bitLength
  )  where

import Data.ByteString
import Data.Hashable
import Rand

newtype Sign = Sign Int deriving Show

newtype NumBits = NumBits Int deriving (Show, Eq)

newtype NumBytes = NumBytes Int deriving Show

class (Show a, Ord a, Num a, Integral a, Hashable a) => INumber a where 

--  factory functions

    zero        :: a
    one         :: a
    fromBytes   :: Sign -> ByteString -> Rand a     -- big-endian, may throw
    random      :: NumBits ->  Rand a               -- uniform 0 .. 2^(numBits) - 1
--  fromInteger :: Integer -> a                     -- inherited from Num

--  instance members

--  (+)         :: a -> a -> a                      -- inherited from Num
--  (*)         :: a -> a -> a                      -- inherited from Num
--  negate      :: a -> a                           -- inherited from Num
    toBytes     :: a -> NumBytes -> Rand ByteString -- b.e. magnitude, may throw
--  signum      :: a -> a                           -- inherited from Num
    sign        :: a -> Int                         -- redundant given signum
    bitLength   :: a -> NumBits
--  toInteger   :: a -> Integer                     -- inherited from Integral
--  show        :: a -> String                      -- inherited from Show
--  (<=)        :: a -> a -> Bool                   -- inherited from Ord
--  (<)         :: a -> a -> Bool                   -- inherited from Ord
--  hash        :: a -> Int                         -- inherited from Hashable
--  (==)        :: a -> a -> Bool                   -- inherited from Eq

-- Only showing API which corresponds to java's implementation

