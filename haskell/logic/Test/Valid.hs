{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Valid
    (   specValid
    )   where


import Test.Hspec
import Test.QuickCheck

import Test.Test

import Formula
import Variable (Var)


specValid :: forall f . (Test f) =>  Spec
specValid = describe "Testing properties of valid..." $ 
    sequence_ (specsValid @ f)

specsValid :: forall f . (Test f) =>  [Spec]
specsValid  = [ testValidSub @ f
              ]

testValidSub :: forall f . (Test f) =>  Spec
testValidSub = it "Checked valid subformula property" $
    property $ propValidSub @ f

propValidSub :: (Test f) =>  (Var -> Var) -> f Var -> Bool
propValidSub f t = valid f t == all (valid f) (sub t)

