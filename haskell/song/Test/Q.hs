module  Test.Q
    (   specQ
    )   where

import           Prelude        hiding  ((+),(*),(-),(/))
import           Data.Proxy
import           Test.Hspec

import           Q
import           Test.Field

specQ :: Spec
specQ = describe "Checking Field Q..." $ 
    sequence_ specsQ

specsQ :: [Spec]
specsQ = map ($ (Proxy :: Proxy Q)) fieldTests


