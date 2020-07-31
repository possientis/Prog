module  Test.List.Intersect
    (   specIntersect
    )   where

import Data.List

import Test.Hspec
import Test.QuickCheck  hiding ((===))

import Variable (Var)

import List.Equiv
import List.Include
import List.Intersect

specIntersect :: Spec
specIntersect = describe "Testing properties of intersect..." $ do
    testInterIntersect
    testInterCharac
    testInterDistribAppR
    testInterConsNotInR
    testInterConsNotInL
    testInterConsInR
    testInterNil
    testInterComm
    testInterAssoc
    testInterCompatL
    testInterCompatR
    testInterCompatLR
    testInterSub
    testInterSub'
    testInterSubEquiv
    testInterDistribAppL 
    testInterAppNilL
    testInterSubNilL
    testInterSubNilR
    testInterConcatNilL

testInterIntersect :: Spec
testInterIntersect = it "Checked inter coincide with GHC 'intersect'" $
    property $ propInterIntersect

testInterCharac :: Spec
testInterCharac = it "Checked inter characterization property" $
    property $ propInterCharac

testInterDistribAppR :: Spec
testInterDistribAppR = it "Checked right-distributivity of (/\\) over (++)" $ do
    property $ propInterDistribAppR

testInterConsNotInR :: Spec
testInterConsNotInR = it "Checked not elem -> xs /\\ (cons y ys) == xs /\\ ys" $ do
    property $ propInterConsNotInR

testInterConsNotInL :: Spec
testInterConsNotInL = it "Checked not elem -> (cons x xs) /\\ ys == xs /\\ ys" $ do
    property $ propInterConsNotInL

testInterConsInR :: Spec
testInterConsInR = it "Checked elem -> xs /\\ (cons y ys) == xs /\\ ys" $ do
    property $ propInterConsInR

testInterNil :: Spec
testInterNil = it "Checked xs /\\ [] == xs" $ do
    property $ propInterNil

testInterComm :: Spec
testInterComm = it "Checked commutativity of /\\" $ do
    property $ propInterComm

testInterAssoc :: Spec
testInterAssoc = it "Checked associativity of /\\" $ do
    property $ propInterAssoc

testInterCompatL :: Spec
testInterCompatL = it "Checked left compatibility of /\\" $ do
    property $ propInterCompatL

testInterCompatR :: Spec
testInterCompatR = it "Checked right compatibility of /\\" $ do
    property $ propInterCompatR

testInterCompatLR :: Spec
testInterCompatLR = it "Checked left-right compatibility of /\\" $ do
    property $ propInterCompatLR

testInterSub :: Spec
testInterSub = it "Checked the sublist property of /\\" $ do
    property $ propInterSub 
 
testInterSub' :: Spec
testInterSub' = it "Checked the sublist' property of /\\" $ do
    property $ propInterSub' 

testInterSubEquiv :: Spec
testInterSubEquiv = it "Checked the sublist equiv property of /\\" $ do
    property $ propInterSubEquiv

testInterDistribAppL :: Spec 
testInterDistribAppL = it "Checked the left-distributivity of (/\\) over (++)" $ do
    property $ propInterDistribAppL

testInterAppNilL :: Spec 
testInterAppNilL = it "Checked the inter app nil left property" $ do
    property $ propInterAppNilL

testInterSubNilL :: Spec 
testInterSubNilL = it "Checked the inter sub nil left property" $ do
    property $ propInterSubNilL

testInterSubNilR :: Spec 
testInterSubNilR = it "Checked the inter sub nil right property" $ do
    property $ propInterSubNilR

testInterConcatNilL :: Spec 
testInterConcatNilL = it "Checked the inter concat nil left property" $ do
    property $ propInterConcatNilL

propInterIntersect :: [Var] -> [Var] -> Bool
propInterIntersect xs ys = xs /\ ys == intersect xs ys

propInterCharac :: [Var] -> [Var] -> Var -> Bool
propInterCharac xs ys z = (z `elem` xs /\ ys) == (z `elem` xs && z `elem` ys)

propInterDistribAppR :: [Var] -> [Var] -> [Var] -> Bool
propInterDistribAppR xs ys zs = (xs ++ ys) /\ zs == (xs /\ zs) ++ (ys /\ zs)

propInterConsNotInR :: [Var] -> [Var] -> Var -> Bool
propInterConsNotInR xs ys y = y `elem` xs || xs /\ (y : ys) == xs /\ ys

propInterConsNotInL :: [Var] -> [Var] -> Var -> Bool
propInterConsNotInL xs ys x = x `elem` ys || (x : xs) /\ ys == xs /\ ys

propInterConsInR :: [Var] -> [Var] -> Var -> Bool
propInterConsInR xs ys y = y `notElem` ys || xs /\ (y : ys) == xs /\ ys 

propInterNil :: [Var] -> Bool
propInterNil xs = xs /\ [] == []

propInterCompatL :: [Var] -> [Var] -> [Var] -> Bool
propInterCompatL xs ys zs = xs /== ys || xs /\ zs === ys /\ zs 

propInterCompatR :: [Var] -> [Var] -> [Var] -> Bool
propInterCompatR xs ys zs = xs /== ys || zs /\ xs === zs /\ ys

propInterCompatLR :: [Var] -> [Var] -> [Var] -> [Var] -> Bool
propInterCompatLR xs xs' ys ys' = xs /== xs' || ys /== ys' ||
    xs /\ ys === xs' /\ ys'

propInterComm :: [Var] -> [Var] -> Bool
propInterComm xs ys = xs /\ ys === ys /\ xs

propInterAssoc :: [Var] -> [Var] -> [Var] -> Bool
propInterAssoc xs ys zs = (xs /\ ys) /\ zs === xs /\ (ys /\ zs)
 
propInterSub :: [Var] -> [Var] -> Bool
propInterSub xs ys = not (xs <== ys) || xs /\ ys === xs 

propInterSub' :: [Var] -> [Var] -> Bool
propInterSub' xs ys = not (xs <== ys) || xs /\ ys == xs 

propInterSubEquiv :: [Var] -> [Var] -> [Var] -> [Var] -> Bool
propInterSubEquiv xs ys zs zs' = not (zs' <== zs) ||
    (zs /\ xs) /== (zs /\ ys) || zs' /\ xs === zs' /\ ys

propInterDistribAppL :: [Var] -> [Var] -> [Var] -> Bool
propInterDistribAppL xs ys zs = zs /\ (xs ++ ys) === (zs /\ xs) ++ (zs /\ ys)

propInterAppNilL :: [Var] -> [Var] -> [Var] -> Bool
propInterAppNilL xs ys zs = zs /\ (xs ++ ys) /= [] ||
      ((zs /\ xs) == [] && (zs /\ ys) == [])

propInterSubNilL :: [Var] -> [Var] -> [Var] -> Bool
propInterSubNilL xs ys zs = not (xs <== ys) || (ys /\ zs) /= [] ||
    (xs /\ zs) == []

propInterSubNilR :: [Var] -> [Var] -> [Var] -> Bool
propInterSubNilR xs ys zs = not (xs <== ys) || (zs /\ ys) /= [] ||
    (zs /\ xs) == []

propInterConcatNilL :: (Var -> [Var]) -> [Var] -> [Var] -> Bool
propInterConcatNilL f xs ys = (not $ all (null . (xs /\) . f) ys) || 
    (xs /\ concatMap f ys) == []

