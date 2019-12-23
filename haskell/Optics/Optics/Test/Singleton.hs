module  Optics.Test.Singleton
    (   specSingleton
    )   where

import Test.Hspec


import Optics.Nat
import Optics.Singleton

specSingleton :: Spec
specSingleton = describe "Testing Singleton..." $ do
    specSBoolTrue
    specSBoolFalse
    specFromSNatZ
    specFromSNatS


specSBoolTrue :: Spec 
specSBoolTrue = it "Checked fromSing STrue" $ do
    fromSing STrue `shouldBe` True


specSBoolFalse :: Spec 
specSBoolFalse = it "Checked fromSing SFalse" $ do
    fromSing SFalse `shouldBe` False

specFromSNatZ :: Spec
specFromSNatZ = it "Checked (fromSNat SZ)" $ do
    fromSing SZ `shouldBe` Z

specFromSNatS :: Spec
specFromSNatS = it "Checked (fromSNat (SS SZ))" $ do
    fromSing (SS SZ) `shouldBe` (S Z)
