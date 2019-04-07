module  Test.Fp
    (   specFp
    )   where

import Data.Proxy
import Test.Hspec

import Fp
import Test.Field

specFp :: Spec
specFp = describe "Checking Field Fp..." $ 
    sequence_ specsFp

proxy :: Proxy Fp
proxy  = Proxy

p :: Integer 
p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

specsFp :: [Spec]
specsFp = testPrime proxy p
        : map ($ proxy) fieldTests


