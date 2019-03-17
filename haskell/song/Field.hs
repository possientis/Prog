{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module  Field
    (   Field (..)
    )   where

import Prelude (Integer, undefined)
import qualified Prelude as P 

data Proxy a = Proxy

class HasPrime a where
    prime :: Proxy a -> Integer

class IsInteger a where
    toInteger   :: a -> Integer
    fromInteger :: Integer -> a 

class Field a where
    (+)    :: a -> a -> a
    (*)    :: a -> a -> a
    (/)    :: a -> a -> a
    inv    :: a -> a
    neg    :: a -> a
    pow    :: a -> Integer -> a
    zero   :: a
    one    :: a 

instance (HasPrime a, IsInteger a) => Field a  where
    (+)  = fieldAdd
    (*)  = fieldMul
    (/)  = fieldDiv
    inv  = fieldInv
    neg  = fieldNeg
    pow  = fieldPow
    zero = fromInteger 0
    one  = fromInteger 1


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

fieldDiv :: (HasPrime a, IsInteger a) => a -> a -> a
fieldDiv = undefined

fieldInv :: (HasPrime a, IsInteger a) => a -> a
fieldInv = undefined

fieldNeg :: (HasPrime a, IsInteger a) => a -> a
fieldNeg = undefined

fieldPow :: (HasPrime a, IsInteger a) => a -> Integer -> a
fieldPow = undefined



