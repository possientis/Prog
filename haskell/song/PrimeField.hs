{-# LANGUAGE ScopedTypeVariables    #-}

module  PrimeField
    (   fieldAdd
    ,   fieldMul 
    ,   fieldInv
    ,   fieldNeg
    ,   fieldPow
    )   where

import Prelude                  (Integer,undefined)
import Data.Proxy
import qualified Prelude as P

import HasPrime
import IsInteger


fieldAdd :: forall a. (HasPrime a, IsInteger a) => a -> a -> a
fieldAdd n m = fromInteger (x P.+ y `P.mod` p)
    where
    p = prime (Proxy :: Proxy a)
    x = toInteger n
    y = toInteger m

fieldMul :: forall a . (HasPrime a, IsInteger a) => a -> a -> a
fieldMul n m = fromInteger (x P.* y `P.mod` p)
    where
    p = prime (Proxy :: Proxy a)
    x = toInteger n
    y = toInteger m

fieldInv :: (HasPrime a, IsInteger a) => a -> a
fieldInv = undefined

fieldNeg :: (HasPrime a, IsInteger a) => a -> a
fieldNeg = undefined

fieldPow :: (HasPrime a, IsInteger a) => a -> Integer -> a
fieldPow = undefined



