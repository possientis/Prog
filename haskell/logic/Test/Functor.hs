{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Functor
    (   specFunctor
    )   where

import Test.Hspec
import Test.QuickCheck

import Test.Test

import Variable  (Var)

specFunctor :: forall f . (Test f) =>  Spec
specFunctor = describe "Testing functor laws..." $
    sequence_ (specsFunctor @ f)

specsFunctor :: forall f . (Test f) =>  [Spec]
specsFunctor =  [testFunctorIdLaw     @ f
                ,testFunctorCompLaw   @ f
                ]

testFunctorIdLaw :: forall f . (Test f) =>  Spec
testFunctorIdLaw = it "Checked functor identity law" $
    property $ propFunctorIdLaw @ f

testFunctorCompLaw :: forall f . (Test f) =>  Spec
testFunctorCompLaw = it "Checked functor composition law" $
    property $ propFunctorCompLaw @ f

propFunctorIdLaw :: (Test f) => f Var -> Bool
propFunctorIdLaw t = fmap id t == t 

propFunctorCompLaw :: (Test f) => (Var -> Var) -> (Var -> Var) -> f Var -> Bool
propFunctorCompLaw g f p = fmap (g . f) p == (fmap g . fmap f) p