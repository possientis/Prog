{-# LANGUAGE GADTs              #-}
{-# LANGUAGE DataKinds          #-}
module  Optics.Test.FinVec
    (   specFinVec
    )   where

import Test.Hspec

import Optics.Nat
import Optics.Vec
import Optics.Fin
import Optics.FinVec

specFinVec :: Spec
specFinVec = describe "Testing FinVec..." $ do
    specVec2IdNil
    specVec2IdCons
    specFin2IdAbsurd
    specFin2IdFin3 


specVec2IdNil :: Spec
specVec2IdNil = it "Checked vec2Id Nil == Nil" $ do
    vec2Id Nil `shouldBe` (Nil :: Vec 'Z Int)

specVec2IdCons :: Spec
specVec2IdCons = it "Checked vec2Id [1,2] == [1,2]" $ do
    vec2Id vec `shouldBe` vec
    where vec = Cons (1 :: Int) (Cons 2 Nil)

specFin2IdAbsurd :: Spec
specFin2IdAbsurd = it "Checked fin2Id absurd == absurd" $ do
    fin2Id (absurd :: Fin 'Z -> Int) `shouldBe` absurd

specFin2IdFin3 :: Spec
specFin2IdFin3 = it "Checked fin2Id [0,1,2] = [0,1,2]" $ do
    fin2Id fun012 == fun012

fun012 :: Fin ('S ('S ('S 'Z)))  -> Int
fun012 FZ = 0
fun012 (FS FZ) = 1
fun012 (FS (FS FZ)) = 2
fun012 (FS (FS (FS _))) = error "should not be called"


