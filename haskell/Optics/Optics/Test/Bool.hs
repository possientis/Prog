module  Optics.Test.Bool
    (   specBool
    ,   SBool
    )   where

import Test.Hspec
import Optics.Bool

specBool :: Spec
specBool = describe "Testing Bool..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
