{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE TypeApplications   #-}

module  Optics.Test.Leq
    (   specLeq
    ,   Leq
    )   where

import Test.Hspec
import Optics.Nat
import Optics.Leq

specLeq :: Spec
specLeq = describe "Testing Leq..." $ do
    specLeqLemma1

specLeqLemma1 :: Spec
specLeqLemma1 = it "Checked lemma1" $ do
    lemma1 `shouldBe` (Le_n @('S 'Z))
