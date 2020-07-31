module  Test.Include
    (   specInclude
    )   where


import Test.Hspec
import Test.QuickCheck

import Include
import Variable (Var)

-- Note that inclusion on lists is *not* antisymmetric

specInclude :: Spec
specInclude = describe "Testing properties for lists inclusion..." $ do
    testInclReflexivity
    testInclTransitivity
    testInclCons2
    testInclApp2
    testInclMap
    testInclConcat
    testInclConcatMap
    testInclNil

testInclReflexivity :: Spec
testInclReflexivity = it "Checked lists inclusion is reflexive" $
    property propInclReflexivity

testInclTransitivity :: Spec
testInclTransitivity = it "Checked lists inclusion is transitive" $
    property propInclTransitivity

testInclCons2 :: Spec
testInclCons2 = it "Checked xs <= ys -> (cons x xs) -> (cons x ys)" $ do
    property propInclCons2

testInclApp2 :: Spec
testInclApp2 = it "Checked ... -> (xs ++ ys) <= (xs' ++ ys')" $ do
    property propInclApp2

testInclMap :: Spec
testInclMap = it "Checked xs <= ys -> map f xs <= map f ys" $ do
    property propInclMap

testInclConcatMap :: Spec
testInclConcatMap = it "Checked x :: xs -> f x <== concat (map f xs)" $ do
    property propInclConcatMap

testInclConcat :: Spec
testInclConcat = it "Checked xss <== yss -> concat xss <== concat yss" $ do
    property propInclConcat

testInclNil :: Spec
testInclNil = it "Checked xs <= nil -> xs == nil" $ do
    property propInclNil

propInclReflexivity :: [Var] -> Bool
propInclReflexivity xs = xs <== xs

-- naive only
propInclTransitivity :: [Var] -> [Var] -> [Var] -> Bool
propInclTransitivity xs ys zs = not (xs <== ys) || not (ys <== zs) 
    || (xs <== zs)

propInclCons2 :: [Var] -> [Var] -> Var -> Bool
propInclCons2 xs ys x = not (xs <== ys) || (x : xs) <== (x : ys)

propInclApp2 :: [Var] -> [Var] -> [Var] -> [Var] -> Bool
propInclApp2 xs xs' ys ys' = not ((xs <== xs') && (ys <== ys')) || 
    (xs ++ ys) <== (xs' ++ ys')

propInclMap :: (Var -> Var) -> [Var] -> [Var] -> Bool
propInclMap f xs ys = not (xs <== ys) || map f xs <== map f ys 

propInclConcat :: [[Var]] -> [[Var]] -> Bool
propInclConcat xss yss = not (xss <== yss) || concat xss <== concat yss

propInclConcatMap :: (Var -> [Var]) -> [Var] -> Var -> Bool
propInclConcatMap f xs x = x `notElem` xs || f x <== concat (map f xs)

propInclNil :: [Var] -> Bool
propInclNil xs = not (xs <= []) || xs == []
