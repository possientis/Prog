module  Optics.Test.If
    (   specIf
    ,   If
    )   where

import Test.Hspec

import Optics.If
import Optics.Singleton

specIf :: Spec
specIf = describe "Testing If..." $ do
    specIfTrue
    specIfFalse

-- seems any failure will happen at compile time anyway
specIfTrue :: Spec
specIfTrue = it "Checked (sIf STrue)" $ do
    sIf STrue (SS (SS SZ)) (SS SZ) `shouldBe` (SS (SS SZ))

-- seems any failure will happen at compile time anyway
specIfFalse :: Spec
specIfFalse = it "Checked (sIf SFalse)" $ do
    sIf SFalse (SS (SS SZ)) (SS SZ) `shouldBe` (SS SZ)



