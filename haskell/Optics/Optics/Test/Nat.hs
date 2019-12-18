module  Optics.Test.Nat
    (   specNat
    ,   Nat
    )   where

import Test.Hspec
import Optics.Nat

specNat :: Spec
specNat = describe "Testing Nat..." $ do
    specFromSNatZ
    specFromSNatS

specFromSNatZ :: Spec
specFromSNatZ = it "Checked (fromSNat SZ)" $ do
    fromSNat SZ `shouldBe` Z

specFromSNatS :: Spec
specFromSNatS = it "Checked (fromSNat (SS SZ))" $ do
    fromSNat (SS SZ) `shouldBe` (S Z)
