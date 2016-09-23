{-# LANGUAGE BangPatterns, ForeignFunctionInterface #-}

-- link with object file lookup3.o, e.g. ghci Hash.hs lookup3.o

module BloomFilter.Hash
  (
    Hashable(..)
  , hash
  , doubleHash
  ) where

import Data.Bits ((.&.), shiftR)
import Foreign.Marshal.Array (withArrayLen)
import Control.Monad (foldM)
import Data.Word (Word32, Word64)
import Foreign.C.Types (CSize(..))
import Foreign.Marshal.Utils (with)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (Storable, peek, sizeOf)
import qualified Data.ByteString as Strict
import qualified Data.ByteString.Lazy as Lazy
import System.IO.Unsafe (unsafePerformIO)

foreign import ccall unsafe "lookup3.h hashword2" 
  hashWord2 :: Ptr Word32 -> CSize -> Ptr Word32 -> Ptr Word32 -> IO ()

foreign import ccall unsafe "lookup3.h hashlittle2"
  hashLittle2 :: Ptr a -> CSize -> Ptr Word32 -> Ptr Word32 -> IO ()

data Hashable = Hashable
hash = undefined
doubleHash = undefined

