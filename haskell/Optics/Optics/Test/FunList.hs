module  Optics.Test.FunList
    (   specFunList
    ,   FunList
    )   where

import Test.Hspec
import Optics.FunList

specFunList :: Spec
specFunList = describe "Testing FunList..." $ do
    it "Checked module compiled" $
        True `shouldBe` True
