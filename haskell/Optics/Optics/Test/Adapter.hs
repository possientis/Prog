module  Optics.Test.Adapter
    (   specAdapter
    ,   Adapter
    )   where

import Test.Hspec
import Optics.Adapter

specAdapter :: Spec
specAdapter = describe "Testing Adapter..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
