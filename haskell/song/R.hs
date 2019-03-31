{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module  R
    (   R (..)
    )   where

import           Prelude hiding   ((+),(-),(*),(/))
import qualified Prelude as P     ((+),(*),(/))
import           Test.QuickCheck


import           Field

eps :: Double
eps = 0.000001

newtype R = R { unR :: Double } deriving (Num, Fractional) 

instance Show R where
    show = show . unR

instance Field R where
    (+)  = (P.+)
    (*)  = (P.*)
    neg  = negate
    inv  = (1 P./)
    zero = 0
    one  = 1

instance Arbitrary R where
    arbitrary = R <$> arbitrary

instance Eq R where
    (==) (R x) (R y) = abs (x - y) < eps

