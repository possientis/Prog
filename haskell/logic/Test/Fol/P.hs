module  Test.Fol.P
    (   specP
    )   where

import Test.Hspec
import Test.QuickCheck

import Fol.P
import Variable  (Var)

specP :: Spec
specP = describe "Testing functor laws for P..." $ 
    sequence_ specsP

specsP :: [Spec]
specsP =  [testFunctorIdLaw
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

