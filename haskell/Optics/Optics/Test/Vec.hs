{-# LANGUAGE DataKinds          #-}

module  Optics.Test.Vec
    (   specVec
    ,   Vec
    )   where

import Prelude      hiding (head)

import Test.Hspec
import Optics.Nat
import Optics.Vec
import Optics.Singleton

specVec :: Spec
specVec = describe "Testing Vec..." $ do
    specVecEq
    specVecToList
    specVecNth
    specVecHead
    specVecAppend
    specVecMakeEven
    specVecReplicate
    specVecTake

specVecEq :: Spec
specVecEq = it "Checked [0,1,2] is equal to its copy" $ do
    (vec012 == vec012') `shouldBe` True

specVecToList :: Spec
specVecToList = it "Checked [0,1,2] is mapped to the list [0,1,2]" $ do
    toList vec012 `shouldBe` [0,1,2]

specVecNth :: Spec
specVecNth = it "Checked function 'nth' on [0,1,2]" $ do
    [nth SZ vec012, nth (SS SZ) vec012, nth (SS (SS SZ)) vec012]
    `shouldBe` [0,1,2]

specVecHead :: Spec
specVecHead = it "Checked function 'head' on [0,1,2]" $ do
    head vec012 `shouldBe` 0

specVecAppend :: Spec
specVecAppend = it "Checked 'append [0,1,2] [3,4]'" $ do
    toList (append vec012 vec34) `shouldBe` [0,1,2,3,4]

specVecMakeEven :: Spec
specVecMakeEven = it "Checked 'makeEven' function" $ do
    [toList (makeEven (SS (SS (SS SZ))) vec012), 
        toList (makeEven (SS (SS SZ)) vec34)] `shouldBe` [[0,0,1,2],[3,4]]

specVecReplicate :: Spec
specVecReplicate = it "Checked 'replicate1 3 0'" $ do
    toList (replicate1 (SS (SS (SS SZ))) (0 :: Int)) `shouldBe` [0,0,0] 

specVecTake :: Spec
specVecTake = it "Checked 'vtake2 2 [0,1,2]'" $ do
    toList (vtake2 (SS (SS SZ)) vec012) `shouldBe` [0,1]

vec012 :: Vec ('S ('S ('S 'Z))) Int
vec012 = Cons 0 (Cons 1 (Cons 2 Nil))

vec34 :: Vec ('S ('S 'Z)) Int
vec34 = Cons 3 (Cons 4 Nil)

vec012' :: Vec ('S ('S ('S 'Z))) Int
vec012' = Cons 0 (Cons 1 (Cons 2 Nil))
