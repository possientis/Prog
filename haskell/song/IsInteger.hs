module  IsInteger
    (   IsInteger   (..)
    )   where

class IsInteger a where
    toInteger   :: a -> Integer
    fromInteger :: Integer -> a
