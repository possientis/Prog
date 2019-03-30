{-# LANGUAGE ScopedTypeVariables    #-}

module  PrimeField
    (   fieldAdd
    ,   fieldMul 
    ,   fieldNeg
    ,   fieldInv
    ,   fieldZero
    ,   fieldOne
    )   where

import Prelude      hiding (fromInteger, toInteger)
import Data.Proxy

import HasPrime
import IsInteger


fieldAdd :: forall a. (HasPrime a, IsInteger a) => a -> a -> a
fieldAdd n m = fromInteger ((x + y) `mod` p)
    where
    p = prime (Proxy :: Proxy a)
    x = toInteger n
    y = toInteger m

fieldMul :: forall a . (HasPrime a, IsInteger a) => a -> a -> a
fieldMul n m = fromInteger ((x * y) `mod` p)
    where
    p = prime (Proxy :: Proxy a)
    x = toInteger n
    y = toInteger m

fieldNeg :: forall a . (HasPrime a, IsInteger a) => a -> a
fieldNeg n = fromInteger ((-x) `mod` p)
    where
    p = prime (Proxy :: Proxy a)
    x = toInteger n


fieldInv :: forall a . (HasPrime a, IsInteger a) => a -> a
fieldInv n
    | x `mod` p == 0    = error "fieldInv: zero has no inverse"
    | otherwise         = fieldPow n (p - 2)
    where
    p = prime (Proxy :: Proxy a)
    x = toInteger n
     
fieldZero :: forall a . (IsInteger a) => a
fieldZero = fromInteger 0

fieldOne :: forall a . (IsInteger a) => a
fieldOne = fromInteger 1

fieldPow :: forall a . (HasPrime a, IsInteger a) => a -> Integer -> a
fieldPow n k 
    | k == 0    = fieldOne
    | k < 0     = fieldInv $ fieldPow n (-k)
    | even k    =       fieldPow (n $*$ n) (k `div` 2)
    | odd  k    = n $*$ fieldPow (n $*$ n) (k `div` 2)
    | otherwise = error "fieldPow: this error should never happen"
    where ($*$) = fieldMul

