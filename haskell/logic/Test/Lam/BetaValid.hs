module  Test.Lam.BetaValid
    (   specBetaValid
    )   where


import Test.Hspec
import Test.QuickCheck


import Variable (Var)
import Lam.T
import Lam.BetaValid

specBetaValid :: Spec
specBetaValid = describe "Testing non-polymorphic properties of BetaValid..." $ do
    testBetaValidVarGen
    testBetaValidVar
    testBetaValidAppGen


testBetaValidVarGen :: Spec
testBetaValidVarGen = it "Checked generic beta validity for variables" $
    property $ propBetaValidVarGen

testBetaValidVar :: Spec
testBetaValidVar = it "Checked beta validity for variables" $
    property $ propBetaValidVar

testBetaValidAppGen :: Spec
testBetaValidAppGen = it "Checked generic beta validity for applications" $
    property $ propBetaValidAppGen

propBetaValidVarGen :: (Var -> T Var) -> Var -> [Var] -> Bool
propBetaValidVarGen f x xs = betaValid_ f xs (Var x)

propBetaValidVar :: (Var -> T Var) -> Var -> Bool
propBetaValidVar f x = betaValid f (Var x)

propBetaValidAppGen :: (Var -> T Var) -> T Var -> T Var -> [Var] -> Bool
propBetaValidAppGen f t1 t2 xs = 
    betaValid_ f xs (App t1 t2) == (betaValid_ f xs t1 && betaValid_ f xs t2)

