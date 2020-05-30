module  Test.Normal
    (   specNormal
    )   where



import Set
import Normal


import Test.Hspec
import Test.QuickCheck

specNormal :: Spec
specNormal = do
    specNormalNormal2


specNormalNormal2 :: Spec
specNormalNormal2 = it "Checked normal = normal2" $ do
    property propNormalNormal2

propNormalNormal2 :: Set -> Bool
propNormalNormal2 x = normal x == normal2 x

