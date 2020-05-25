module  Test.Set
    (   specSet
    )   where

import Set
import Incl
import Equal
import Elem

import Test.Hspec

specSet :: Spec
specSet = do
    it "Testing 0 <= 1 " $ zero <== one     `shouldBe` True
    it "Testing 1 <= 2 " $ one <== two      `shouldBe` True
    it "Testing 2 <= 3 " $ two <== three    `shouldBe` True
    it "Testing 3 <= 4 " $ three <== four   `shouldBe` True
    it "Testing 4 <= 5 " $ four <== five    `shouldBe` True
    it "Testing 0 == 0 " $ zero === zero    `shouldBe` True
    it "Testing 1 == 1 " $ one === one      `shouldBe` True
    it "Testing 2 == 2 " $ two === two      `shouldBe` True
    it "Testing 3 == 3 " $ three === three  `shouldBe` True
    it "Testing 4 == 4 " $ four === four    `shouldBe` True
    it "Testing 5 == 5 " $ five === five    `shouldBe` True
    it "Testing 5 == {0} \\/ 5" $ (Cons zero five)  === five `shouldBe` True
    it "Testing 5 == {1} \\/ 5" $ (Cons one five)   === five `shouldBe` True
    it "Testing 5 == {2} \\/ 5" $ (Cons two five)   === five `shouldBe` True
    it "Testing 5 == {3} \\/ 5" $ (Cons three five) === five `shouldBe` True
    it "Testing 5 == {4} \\/ 5" $ (Cons four five)  === five `shouldBe` True
    it "Testing 5 /= {5} \\/ 5" $ (Cons five five)  === five `shouldBe` False
    it "Testing 0 : 5"  $ zero  <: five `shouldBe` True
    it "Testing 1 : 5"  $ one   <: five `shouldBe` True
    it "Testing 2 : 5"  $ two   <: five `shouldBe` True
    it "Testing 3 : 5"  $ three <: five `shouldBe` True
    it "Testing 4 : 5"  $ four  <: five `shouldBe` True
    it "Testing ¬5 : 5" $ five  <: five`shouldBe` False
