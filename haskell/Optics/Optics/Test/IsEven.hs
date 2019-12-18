module  Optics.Test.IsEven
    (   specIsEven
    ,   IsEven
    )   where

import Test.Hspec
import Optics.IsEven

specIsEven :: Spec
specIsEven = describe "Testing IsEven..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
