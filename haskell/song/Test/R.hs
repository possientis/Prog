module  Test.R
    (   specR
    )   where

import           Prelude        hiding  ((+),(*),(-),(/))
import           Data.Proxy
import           Test.Hspec

import           R
import           Test.Field

specR :: Spec
specR = describe "Checking Field R..." $ 
    sequence_ specsR

specsR :: [Spec]
specsR = map ($ (Proxy :: Proxy R)) fieldTests


