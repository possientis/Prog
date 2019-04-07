{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module  Q
    (   Q (..)
    )   where

import           Prelude hiding   ((+),(-),(*),(/))
import qualified Prelude as P     ((+),(*),(/))
import           Test.QuickCheck


import           Field

newtype Q = Q { unQ :: Rational } deriving (Eq, Num, Fractional) 

instance Show Q where
    show = show . unQ

instance Field Q where
    (+)  = (P.+)
    (*)  = (P.*)
    neg  = negate
    inv  = (1 P./)
    zero = 0
    one  = 1

instance Arbitrary Q where
    arbitrary = Q <$> arbitrary

