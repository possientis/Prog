module  Test.F13
    (   specF13
    )   where

import           Prelude        hiding  ((+),(*),(-),(/))
import           Data.Proxy
import           Test.Hspec

import           F13
import           Test.Field

specF13 :: Spec
specF13 = describe "Checking Field F13..." $ 
    sequence_ specsF13

specsF13 :: [Spec]
specsF13 = map ($ (Proxy :: Proxy F13)) fieldTests


