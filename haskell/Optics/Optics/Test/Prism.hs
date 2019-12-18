module  Optics.Test.Prism
    (   specPrism
    ,   Prism
    )   where

import Test.Hspec
import Optics.Prism

specPrism :: Spec
specPrism = describe "Testing Prism..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
