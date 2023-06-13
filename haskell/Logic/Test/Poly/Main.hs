{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module  Test.Poly.Main
    (   specPoly
    )   where

import Test.Hspec

import Test.Poly.Test
import Test.Poly.Free
import Test.Poly.Dmap
import Test.Poly.Bound
import Test.Poly.Valid
import Test.Poly.Functor
import Test.Poly.Variable
import Test.Poly.LocalInv
import Test.Poly.Subformula

specPoly :: forall f . (Test f) =>  Spec
specPoly = do
    specFunctor     @f
    specSubformula  @f
    specVariable    @f
    specFree        @f
    specBound       @f
    specValid       @f
    specDmap        @f
    specLocalInv    @f
   
