{-# LANGUAGE DataKinds  #-}

module  Test.Mod13
    (   specMod13
    )   where

import Data.Proxy
import Test.Hspec

import Modular
import Test.Field

specMod13 :: Spec
specMod13 = describe "Checking Field Mod13..." $ 
    sequence_ specsMod13

proxy :: Proxy (Mod 13)
proxy  = Proxy

specsMod13 :: [Spec]
specsMod13 = testPrime proxy 13 
           : map ($ proxy) fieldTests


