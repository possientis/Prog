module  Test.F13
    (   specF13
    )   where

import Data.Proxy
import Test.Hspec

import F13
import Test.Field

specF13 :: Spec
specF13 = describe "Checking Field F13..." $ 
    sequence_ specsF13

proxy :: Proxy F13
proxy  = Proxy

specsF13 :: [Spec]
specsF13 = testPrime proxy 13
         : map ($ proxy) fieldTests


