{-# LANGUAGE DataKinds  #-}

module  Test.Modp
    (   specModp
    )   where

import Data.Proxy
import Test.Hspec

import Modp
import Test.Field

specModp :: Spec
specModp = describe "Checking Field Modp..." $ 
    sequence_ specsModp

proxy :: Proxy Modp
proxy  = Proxy

p :: Integer 
p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

specsModp :: [Spec]
specsModp = testPrime proxy p
           : map ($ proxy) fieldTests


