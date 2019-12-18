module  Optics.Test.Plus
    (   specPlus
    ,   Plus
    )   where

import Test.Hspec
import Optics.Plus

specPlus :: Spec
specPlus = describe "Testing Plus..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
