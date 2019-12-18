module  Optics.Test.Leq
    (   specLeq
    ,   Leq
    )   where

import Test.Hspec
import Optics.Leq

specLeq :: Spec
specLeq = describe "Testing Leq..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
