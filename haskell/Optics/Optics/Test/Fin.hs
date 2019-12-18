{-# LANGUAGE GADTs              #-}
{-# LANGUAGE DataKinds          #-}

module  Optics.Test.Fin
    (   specFin
    ,   Fin
    )   where

import Test.Hspec
import Optics.Nat
import Optics.Fin

specFin :: Spec
specFin = describe "Testing Fin..." $ do
    specFinAbsurd
    specFinFun012
    specFinFun345
    specToList


specFinAbsurd :: Spec
specFinAbsurd = it "Checked absurd == absurd" $ do
    ((absurd :: Fin 'Z -> Int) == absurd) `shouldBe` True

specFinFun012 :: Spec
specFinFun012 = it "Checked function [0,1,2] equal to copy of itself" $ do
    (fun012 == fun012') `shouldBe` True

specFinFun345 :: Spec
specFinFun345 = it "Checked function [0,1,2] not equal to [3,4,5]" $ do
    (fun012 /= fun345) `shouldBe` True


specToList :: Spec
specToList = it "Checked function [0,1,2] is mapped to list [0,1,2]" $ do
    toList fun012 `shouldBe` [0,1,2]



fun012 :: Fin ('S ('S ('S 'Z)))  -> Int
fun012 FZ = 0
fun012 (FS FZ) = 1
fun012 (FS (FS FZ)) = 2
fun012 (FS (FS (FS _))) = error "should not be called"

fun345 :: Fin ('S ('S ('S 'Z)))  -> Int
fun345 FZ = 3
fun345 (FS FZ) = 4
fun345 (FS (FS FZ)) = 5
fun345 (FS (FS (FS _))) = error "should not be called"

fun012' :: Fin ('S ('S ('S 'Z)))  -> Int
fun012' FZ = 0
fun012' (FS FZ) = 1
fun012' (FS (FS FZ)) = 2
fun012' (FS (FS (FS _))) = error "should not be called"

