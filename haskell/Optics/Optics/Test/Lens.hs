module  Optics.Test.Lens
    (   specLens
    ,   Lens
    )   where

import Test.Hspec
import Optics.Lens

specLens :: Spec
specLens = describe "Testing Lens..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
