module  Test.Pretty
    (   specPretty
    )   where

import DSL
import Pretty

import Test.Hspec
import Test.QuickCheck


specPretty :: Spec
specPretty = describe "Checking the Pretty module..." $ do
    specENum
    specEBool
    specEAdd
    specEMul
    specESub
    specEDiv
    specEAnd
    specEOr
    specEImp
    specENot
    specELe
    specEEq
    specEZero
    specESuc
    specEVar
    specEIf
    specELam
    specEApp
    specEApp2
    specERec
    specECase
    specEFac
    

specENum :: Spec
specENum = it "Checked showExpr for eNum" $ 
    property propENum

specEBool :: Spec
specEBool = it "Checked showExpr for eBool" $ 
    property propEBool

specEAdd :: Spec
specEAdd = it "Checked showExpr for eAdd" $
    property propEAdd

specEMul :: Spec
specEMul = it "Checked showExpr for eMul" $
    property propEMul

specESub :: Spec
specESub = it "Checked showExpr for eSub" $
    property propESub

specEDiv :: Spec
specEDiv = it "Checked showExpr for eDiv" $
    property propEDiv

specEAnd :: Spec
specEAnd = it "Checked showExpr for eAnd" $
    property propEAnd

specEOr :: Spec
specEOr = it "Checked showExpr for eOr" $
    property propEOr

specEImp :: Spec
specEImp = it "Checked showExpr for eImp" $
    property propEImp

specENot :: Spec
specENot = it "Checked showExpr for eNot" $
    property propENot

specELe :: Spec
specELe = it "Checked showExpr for eLe" $
    property propELe

specEEq :: Spec
specEEq = it "Checked showExpr for eEq" $
    property propEEq

specEZero :: Spec
specEZero = it "Checked showExpr for eZero" $
    showExpr eZero `shouldBe` "zero"

specESuc :: Spec
specESuc = it "Checked showExpr for eSuc" $
    property propESuc

specEVar :: Spec
specEVar = it "Checked showExpr for eVar" $
    property propEVar

specEIf :: Spec
specEIf = it "Checked showExpr for eIf" $ showExpr 
    (eIf (eEq (eVar "x") (eVar "y")) 
        (eNum 5) 
        (eAdd (eVar "x") (eVar "y"))) `shouldBe`
    "if x == y then 5 else x + y"

specELam :: Spec
specELam = it "Checked showExpr for eLam" $ showExpr
    (eLam "x" (eLam "y" (eAdd (eVar "x") (eVar "y")))) `shouldBe`
    "\\x y -> x + y"

specEApp :: Spec
specEApp = it "Checked showExpr for eApp" $ showExpr
    (eApp (eVar "f") (eVar "x")) `shouldBe` "f x"

specEApp2 :: Spec
specEApp2 = it "Checked showExpr for eApp2" $ showExpr
    (eApp2 (eVar "f") (eVar "x") (eVar "y")) `shouldBe` "(f x) y"

specERec :: Spec
specERec = it "Checked showExpr for eRec" $ showExpr
    (eRec "f" (eLam "x" (eAdd (eNum 1) (eApp (eVar "f") (eVar "x"))))) `shouldBe`
    "fix f := \\x -> 1 + (f x)"

specECase :: Spec
specECase = it "Checked showExpr for eCase" $ showExpr
    (eCase (eVar "n") 
        (eVar "m") 
        "n" (eSuc (eApp2 (eVar "f") (eVar "n") (eVar "m"))))
    `shouldBe`
    "case n of | zero => m | suc n => suc ((f n) m)"

specEFac :: Spec
specEFac = it "Checked showExpr for eFac" $ showExpr eFac `shouldBe`
   "fix f := \\n -> if n <= 0 then 1 else n * (f (n - 1))" 
    
propENum :: Integer -> Bool
propENum n = showExpr (eNum n) == show n

propEBool :: Bool -> Bool
propEBool b = showExpr (eBool b) == show b

propEAdd :: Integer -> Integer -> Bool
propEAdd n m = showExpr (eAdd (eNum n) (eNum m)) == show n ++ " + " ++ show m

propEMul :: Integer -> Integer -> Bool
propEMul n m = showExpr (eMul (eNum n) (eNum m)) == show n ++ " * " ++ show m

propESub :: Integer -> Integer -> Bool
propESub n m = showExpr (eSub (eNum n) (eNum m)) == show n ++ " - " ++ show m

propEDiv :: Integer -> Integer -> Bool
propEDiv n m = showExpr (eDiv (eNum n) (eNum m)) == show n ++ " / " ++ show m

propEAnd :: Bool -> Bool -> Bool
propEAnd x y = showExpr (eAnd (eBool x) (eBool y)) == show x ++ " /\\ " ++ show y

propEOr :: Bool -> Bool -> Bool
propEOr x y = showExpr (eOr (eBool x) (eBool y)) == show x ++ " \\/ " ++ show y

propEImp :: Bool -> Bool -> Bool
propEImp x y = showExpr (eImp (eBool x) (eBool y)) == show x ++ " => " ++ show y

propENot :: Bool -> Bool
propENot x = showExpr (eNot (eBool x)) == "¬" ++ show x

propELe :: Integer -> Integer -> Bool
propELe n m = showExpr (eLe (eNum n) (eNum m)) == show n ++ " <= " ++ show m

propEEq :: Integer -> Integer -> Bool
propEEq n m = showExpr (eEq (eNum n) (eNum m)) == show n ++ " == " ++ show m

propESuc :: Integer -> Bool
propESuc n = (n <= 0) && showExpr (eSuc (eNat n)) == "suc zero"
           || showExpr (eSuc (eNat n)) == "suc (" ++ showExpr (eNat n) ++ ")"

propEVar :: String -> Bool
propEVar s = showExpr (eVar s) == s

