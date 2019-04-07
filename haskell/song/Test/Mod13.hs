{-# LANGUAGE DataKinds  #-}

module  Test.Mod13
    (   specMod13
    )   where

import           Prelude        hiding  ((+),(*),(-),(/))
import           Data.Proxy
import           Test.Hspec

import           Modular
import           Test.Field

specMod13 :: Spec
specMod13 = describe "Checking Field Mod13..." $ 
    sequence_ specsMod13

specsMod13 :: [Spec]
specsMod13 = map ($ (Proxy :: Proxy (Mod 13))) fieldTests


