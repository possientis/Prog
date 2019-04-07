module  Test.Q
    (   specQ
    )   where

import Data.Proxy
import Test.Hspec

import Q
import Test.Field

specQ :: Spec
specQ = describe "Checking Field Q..." $ 
    sequence_ specsQ

proxy :: Proxy Q
proxy  = Proxy

specsQ :: [Spec]
specsQ = map ($ proxy) fieldTests


