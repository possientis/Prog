module BloomFilter.Internal
  (
    Bloom(..)
  , MutBloom(..)
  ) where

import Data.Word (Word32)
import Data.Array.Unboxed (UArray)
import Data.Array.ST (STUArray)

data Bloom a = B {
    blmHash   :: (a -> [Word32])
  , blmArray  :: UArray Word32 Bool
  }

data MutBloom s a = MB {
    mutHash   :: (a -> [Word32])
  , mutArray  :: STUArray s Word32 Bool
  }





