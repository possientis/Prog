module  Fol.Haskell.Test
    (   test
    )   where

import Test.Hspec
import Test.QuickCheck

import Fol.Haskell.P
import Haskell.Variable  (Var)

test :: Spec
test = describe "Testing Haskell for Fol..." $ 
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

propFunctorIdLaw :: P Var -> Bool
propFunctorIdLaw p = fmap id p == p 

propFunctorCompLaw :: (Var -> Var) -> (Var -> Var) -> P Var -> Bool
propFunctorCompLaw g f p = fmap (g . f) p == (fmap g . fmap f) p

