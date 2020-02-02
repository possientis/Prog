module  Optics.Test.Prism
    (   specPrism
    ,   PrismC
    )   where

import Test.Hspec
import Optics.Prism

specPrism :: Spec
specPrism = describe "Testing Prism..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
