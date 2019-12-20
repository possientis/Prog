module  Optics.Test.Plus
    (   specPlus
    ,   Plus
    )   where

import Test.Hspec
import Optics.Nat
import Optics.Plus

specPlus :: Spec
specPlus = describe "Testing Plus..." $ do
    specPlus23

-- seems very difficult to fail that test without compile time error 
specPlus23 :: Spec
specPlus23 = it "Checked sPLus 2 3" $ do
    sPlus (SS (SS SZ)) (SS (SS (SS SZ))) `shouldBe` (SS (SS (SS (SS (SS SZ)))))


