module Number 
  ( Number
  , NumBytes(..)
  , NumBits(..)
  , Sign(..)
  , Rand
  , toIO
  , fromIO
  , rand
  , zero
  , one
  , fromBytes
  , random
  , toBytes
  , bitLength
  , sign
  , hash
  ) where

-- choose implementation here

import Number1

type Number = Number1

