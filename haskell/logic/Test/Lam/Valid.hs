module  Test.Lam.Valid
    (   specValid
    )   where


import Test.Hspec
import Test.QuickCheck

import Variable (Var)
import Formula
import Lam.T

specValid :: Spec
specValid = describe "Testing non-polymorphic properties of valid..." $ do
    testValidVar
    testValidApp
    testValidLam
    testValidCharac

testValidVar :: Spec
testValidVar = it "Checked valid var property" $
    property $ propValidVar

testValidApp :: Spec
testValidApp = it "Checked valid app property" $ 
    property $ propValidApp

testValidLam :: Spec
testValidLam = it "Checked valid lam property" $ 
    property $ propValidLam

testValidCharac :: Spec
testValidCharac = it "Checked valid characterization property" $ 
    property $ propValidCharac

propValidVar :: (Var -> Var) -> Var -> Bool
propValidVar f x = valid f (Var x) 

propValidApp :: (Var -> Var) -> T Var -> T Var -> Bool
propValidApp f t1 t2 = valid f (App t1 t2) == (valid f t1 && valid f t2)

propValidLam :: (Var -> Var) -> T Var -> Var -> Bool
propValidLam f t1 x = valid f (Lam x t1) == 
   (valid f t1 && all ((/= f x) . f) (free $ Lam x t1))

propValidCharac :: (Var -> Var) -> T Var -> Bool
propValidCharac f t = valid f t == all cond (sub t) where
    cond :: T Var -> Bool
    cond t'@(Lam x _) = all ((/= f x) . f) (free t')
    cond _            = True
