module  Optics.Test.Lens
    (   specLens
    ,   LensC
    )   where

import Test.Hspec
import Optics.Lens

specLens :: Spec
specLens = describe "Testing Lens..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
