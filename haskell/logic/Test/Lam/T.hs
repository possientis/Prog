module  Test.Lam.T
    (   specT
    )   where

import Test.Hspec
import Test.QuickCheck

import Lam.T
import Variable  (Var)

specT :: Spec
specT = describe "Testing functor laws for T..." $
    sequence_ specsT

specsT :: [Spec]
specsT =  [testFunctorIdLaw
          ,testFunctorCompLaw
          ]

testFunctorIdLaw :: Spec
testFunctorIdLaw = it "Checked functor identity law" $
    property $ propFunctorIdLaw

testFunctorCompLaw :: Spec
testFunctorCompLaw = it "Checked functor composition law" $
    property $ propFunctorCompLaw

propFunctorIdLaw :: T Var -> Bool
propFunctorIdLaw t = fmap id t == t 

propFunctorCompLaw :: (Var -> Var) -> (Var -> Var) -> T Var -> Bool
propFunctorCompLaw g f p = fmap (g . f) p == (fmap g . fmap f) p
