module  Lam.Haskell.Test
    (   test
    )   where

import Test.Hspec
import Test.QuickCheck

import Lam.Haskell.T
import Haskell.Variable  (Var)

test :: Spec
test = describe "Testing Haskell for Lam..." $
    sequence_ tests

tests :: [Spec]
tests =  [testFunctorIdLaw
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
