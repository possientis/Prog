module  Test.RanAccess
    (   specRanAccess
    )   where


import Test.Hspec
--import Test.QuickCheck

import Tree
import RanAccess

specRanAccess :: Spec
specRanAccess = do
    specEx1
    specEx2


specEx1 :: Spec
specEx1 = it "Checked fromRA ex1 == [1,2,3,4,5,6]" $ do
    fromRA ex1 `shouldBe` [1,2,3,4,5,6]

specEx2 :: Spec
specEx2 = it "Checked fromRA ex2 == [1,2,3,4,5]" $ do
    fromRA ex2 `shouldBe` [1,2,3,4,5]


-- 110 is binary representation of 6. List [1,2,3,4,5,6]
ex1 :: RAList Int
ex1 = RAList 
    [ Zero
    , One (node (leaf 1) (leaf 2)) 
    , One (node (node (leaf 3) (leaf 4)) (node (leaf 5) (leaf 6)))
    ]

-- 101 is binary representation of 5. List [1,2,3,4,5]
ex2 :: RAList Int
ex2 = RAList
    [ One (leaf 1)
    , Zero
    , One (node (node (leaf 2) (leaf 3)) (node (leaf 4) (leaf 5)))
    ]
