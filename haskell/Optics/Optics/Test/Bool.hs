module  Optics.Test.Bool
    (   specBool
    ,   SBool
    )   where

import Test.Hspec
import Optics.Bool

specBool :: Spec
specBool = describe "Testing Bool..." $ do
    specBoolTrue
    specBoolFalse


specBoolTrue :: Spec 
specBoolTrue = it "Checked fromSBool STrue" $ do
    fromSBool STrue `shouldBe` True


specBoolFalse :: Spec 
specBoolFalse = it "Checked fromSBool SFalse" $ do
    fromSBool SFalse `shouldBe` False
