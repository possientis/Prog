{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Poly.Dmap
    (   specDmap
    )   where

import Test.Hspec
import Test.QuickCheck


import Test.Poly.Test

import Formula
import Variable (Var)

specDmap :: forall f . (Test f) => Spec
specDmap = describe "Testing properties of dmap..." $ do 
    testDmapId  @f


testDmapId :: forall f . (Test f) => Spec
testDmapId = it "Checked dmap id property" $
    property $ propDmapId @f

propDmapId :: (Test f) => f Var -> Bool
propDmapId t = dmap id id t == t

