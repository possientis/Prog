module  Test.Include
    (   specInclude
    )   where


import Test.Hspec
import Test.QuickCheck

import Include
import Variable (Var)

specInclude :: Spec
specInclude = describe "Testing properties for lists inclusion..." $
    sequence_ specsInclude

-- Note that inclusion on lists is *not* antisymmetric

specsInclude :: [Spec]
specsInclude  = [ testInclReflexivity
                , testInclTransitivity
                ]


testInclReflexivity :: Spec
testInclReflexivity = it "Checked lists inclusion is reflexive" $
    property $ propInclReflexivity

testInclTransitivity :: Spec
testInclTransitivity = it "Checked lists inclusion is transitive" $
    property $ propInclTransitivity

propInclReflexivity :: [Var] -> Bool
propInclReflexivity xs = incl xs xs

-- naive only
propInclTransitivity :: [Var] -> [Var] -> [Var] -> Bool
propInclTransitivity xs ys zs = not (incl xs ys) || not (incl ys zs) 
    || (incl xs zs)




