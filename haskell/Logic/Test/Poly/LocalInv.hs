{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}


module  Test.Poly.LocalInv
    (   specLocalInv
    )   where

import Test.Hspec
import Test.QuickCheck


import Test.Poly.Test

import Formula
import Variable (Var, mainVars)

import List.Include
import List.Intersect
import List.Difference

specLocalInv :: forall f . (Test f) => Spec
specLocalInv = describe "Testing properties of LocalInv..." $ do 
    testLocalInvLemma   @f

testLocalInvLemma :: forall f . (Test f) => Spec
testLocalInvLemma = it "Checked local inversion lemma" $
    property $ propLocalInvLemma @f

-- Don't expect this test to achieve much, but at least approximate statement
propLocalInvLemma 
    :: (Test f) 
    => (Var -> Var)
    -> [Var]
    -> [Var]
    -> (Var -> Var)
    -> (Var -> Var)
    -> [Var]
    -> f Var
    -> Bool
propLocalInvLemma f v0 v1 g0 g1 xs t =
    any (\x -> (x `elem` v0) && g0 (f x) /= x) mainVars ||  -- very dodgy
    any (\x -> (x `elem` v1) && g1 (f x) /= x) mainVars ||  -- very dodgy
    not (bnd t ++ xs <== v0) ||
    not (free t \\ xs  <== v1) ||
    not (valid f t) ||
    map f xs /\ map f (free t \\ xs) /= [] ||
    dmap_ g0 g1 (map f xs) (fmap f t) == t
