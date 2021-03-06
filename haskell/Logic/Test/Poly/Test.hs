{-# LANGUAGE ConstraintKinds        #-}

module  Test.Poly.Test
    (   Test
    )   where

import Test.QuickCheck

import Formula
import Variable (Var)

type Test f = (Formula f, Eq (f Var), Show (f Var), Arbitrary (f Var)) 
