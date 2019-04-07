module  Test.Fp
    (   specFp
    )   where

import           Prelude        hiding  ((+),(*),(-),(/))
import           Data.Proxy
import           Test.Hspec

import           Fp
import           Test.Field

specFp :: Spec
specFp = describe "Checking Field Fp..." $ 
    sequence_ specsFp

specsFp :: [Spec]
specsFp = map ($ (Proxy :: Proxy Fp)) fieldTests


