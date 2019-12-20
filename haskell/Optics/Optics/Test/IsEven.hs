module  Optics.Test.IsEven
    (   specIsEven
    ,   IsEven
    )   where

import Test.Hspec

import Optics.Nat
import Optics.Bool
import Optics.IsEven

specIsEven :: Spec
specIsEven = describe "Testing IsEven..." $ do
    specIsEven0
    specIsEven1
    specIsEven2

-- seems very difficult to fail that test without compile-time error
specIsEven0 :: Spec
specIsEven0 = it "Checked sIsEven 0" $ do
    sIsEven SZ `shouldBe` STrue

-- seems very difficult to fail that test without compile-time error
specIsEven1 :: Spec
specIsEven1 = it "Checked sIsEven 1" $ do
    sIsEven (SS SZ) `shouldBe` SFalse

-- seems very difficult to fail that test without compile-time error
specIsEven2 :: Spec
specIsEven2 = it "Checked sIsEven 2" $ do
    sIsEven (SS (SS SZ)) `shouldBe` STrue

