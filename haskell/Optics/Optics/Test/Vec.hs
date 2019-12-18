module  Optics.Test.Vec
    (   specVec
    ,   Vec
    )   where

import Test.Hspec
import Optics.Vec

specVec :: Spec
specVec = describe "Testing Vec..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
