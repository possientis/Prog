module  HasPrime
    (   HasPrime    (..)
    )   where

import Data.Proxy

class HasPrime a where
    prime :: Proxy a -> Integer


